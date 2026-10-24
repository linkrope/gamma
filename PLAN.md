# LALR Parser Integration Plan

## Objective

Add LALR as an alternative generated-parser backend while keeping Epsilon's
single-sweep and SOAG evaluator generators alive during the Gamma/Epsilon
migration.

The final runtime path is:

```text
generated lexer -> table-driven LALR parser -> Gamma ParseTree
                -> removable Gamma-to-Epsilon transformation
                -> Epsilon Tree/PosTree -> generated evaluator
```

SLAG is excluded: its evaluator works in lock-step with an ELL parser and
cannot consume a completed LALR tree.

## Current state

`--lalr` is not yet a compiler backend.  `gamma.main.check` generates
`parser-tables.json`, then `gamma.main.compile` immediately returns.  No
lexer, generated compiler, parser execution, evaluator, or compiler output is
produced for that option.

## Agreed design

- `--lalr` selects LALR.  It skips the ELL(1) suitability check and is an
  error with `--slag`.
- LALR supports single-sweep and SOAG only.  Keep the existing preference:
  single-sweep first, SOAG second.
- The LALR runtime owns a Gamma parse tree and contains no Epsilon IDs, heap
  addresses, evaluator code, or predicate nodes.
- Define `ParseNode` as a recursive `std.sumtype.SumType` with separate
  `Terminal` and `Rule` variants.  Rule children use `This*[]` or equivalent
  indirection.  Do not add a visitor hierarchy or extend
  `gamma.runtime.Node`.
- A terminal stores its parser-table terminal ID, start-only `io.Position`,
  and synthetic flag.  A rule stores its stable table `ruleAlt` ID, start
  position, and ordered children.  Shift creates a terminal; reduce creates a
  rule.
- `ParseTree` contains the user grammar start-symbol root and final lexer
  cursor position.  The augmented `(Start)` rule and EOF are parser machinery,
  not tree nodes.
- `ParseTree.toString` emits deterministic GraphViz DOT.  Inner nodes show
  their LHS nonterminal name and leaves show terminal representations.  Do
  not print pointer addresses.
- The existing generated Epsilon lexer remains unchanged.  A small generated
  wrapper calls `S.Get(Tok)`, exposes `S.Pos`, and maps lexer token IDs to the
  compact table terminal IDs, including lexer EOF to table `(end)`.
- Predicate nodes are omitted because they derive the empty word ambiguously.
  The later transformation obtains their runtime position from the next real
  terminal leaf in source order, or from `ParseTree.endPosition` at EOF.
- `ParserGrammarBuilder` must preserve a map from each cloned parser
  alternative to its source `plainHyperGrammar` alternative.  Parser grammar
  IDs remain compact.  The mapping is later emitted as a `ruleAlt` projection;
  never reconstruct it by names or BNF-shape guesses.
- Gamma lowers EBNF options and repetitions into anonymous BNF nonterminals.
  The Epsilon transformation must fold them into Epsilon's logical
  `Opt`/`Rep` rules, including their distinguished empty alternative.
- On recovered input, eventually return a best-effort tree with synthetic
  terminals at `UndefPos`, but never transform or evaluate it when the parser
  error count is nonzero.
- The Epsilon bridge is separate and removable: it transforms a completed
  Gamma tree into the existing Epsilon `Tree`/`PosTree` evaluator ABI, rather
  than making the LALR parser construct Epsilon heap records directly.
- Consecutive predicate factors receive the same next-visible-terminal
  position during transformation.

## Implementation steps

### 1. Generate a parser-only LALR executable

Replace the `--lalr` early return with the smallest executable backend.  For
an EAG, Gamma must generate and build a compiler that:

1. generates the existing lexer;
2. embeds the currently generated single parser-table file using D's `import`
   expression;
3. runs `gamma.runtime.lr.LR1Parser` through the generated lexer
   wrapper;
4. stops immediately on the first syntax error with a failing process status;
   and
5. prints `OK` on valid input.

This step deliberately has no parse tree, recovery tree, Epsilon evaluator,
or compiler output.  It proves that the generated lexer, token mapping,
embedded current table format, and table-driven LALR runtime work in one
executable.  Retain the current JSON table for this intermediate step; do not
add extra sidecar mapping files.

Add a valid-input generated-compiler integration test expecting `OK` and an
invalid-input test expecting failure.

Checkpoint:

```sh
dub build
dub test
dub test --config=example
```

## Follow-up

Make the single-sweep evaluator work with `--lalr`. Once it is supported,
stop forcing SOAG as the only LALR evaluator and allow `--lalr --sweep`.

### 2. Add the parser-tree model

Add focused LALR runtime types for `ParseTree`, recursive `SumType` nodes,
and GraphViz rendering.  Keep them distinct from grammar-definition nodes.

Enforce these invariants:

- a nonempty reduction uses its first child position;
- an empty reduction uses the current lookahead position;
- child order is parser-RHS order;
- root is the user start symbol; and
- final cursor position is retained separately.

Add permanent unit tests for terminal/rule distinction, rule IDs, child order,
positions, root selection, and deterministic DOT.

Checkpoint:

```sh
dub build
dub test
dub test --config=example
```

### 3. Construct the tree during shift and reduce

Maintain a semantic stack alongside LR states in `LR1Parser`.

- Shift pushes a terminal node.
- Reduce pops exactly the RHS count, restores left-to-right order, creates a
  rule node with `ruleAlt`, and pushes it.
- Halt discards the EOF semantic value and returns the existing user-start
  node; never create the augmented-start node.
- Correct the existing `ParserStack.pop` contract before depending on it in
  debug builds.
- Preserve table display metadata for DOT labels.

Use a temporary runtime fixture with the current table writer/reader and a
test scanner to inspect a DOT tree.  It can be removed after end-to-end LALR
evaluator coverage exists.

Checkpoint:

```sh
dub build
dub test
dub test --config=example
```

### 4. Print trees from generated LALR compilers

Change the parser-only compiler from step 1 so valid input prints
`ParseTree.toString` instead of `OK`.  Keep the same lexer wrapper and
embedded current table.  Do not yet generate or call an Epsilon evaluator.

Checkpoint:

```sh
dub build
dub test
dub test --config=example
```

### 5. Add recovery-tree replay

After valid-input trees are correct, extend LR repair simulation to maintain
semantic values as well as LR states.  Inserted terminals are synthetic with
`UndefPos`; successful recovery returns an error-marked best-effort tree.
Transformation and evaluation remain disabled when errors occurred.  Add
focused recovery tests before enabling any evaluator path for repaired input.

Checkpoint:

```sh
dub build
dub test
dub test --config=example
```

### 6. Preserve parser-to-EAG provenance

Make `ParserGrammarBuilder` return both the cloned parser grammar and cloned
parser-alternative -> source plain-grammar-alternative mapping.  At table
emission, derive stable `ruleAlt`-keyed projection data from it.  This uses
the existing anonymous-nonterminal identities that connect plain BNF to the
original EBNF and Epsilon EAG representations.  Retain compact parser symbol
IDs for table size; do not attempt to preserve source IDs in parser tables.

Checkpoint:

```sh
dub build
dub test
dub test --config=example
```

### 7. Implement the removable Gamma-to-Epsilon transformation

Generate a separate module that transforms a completed Gamma tree into the
existing Epsilon `Tree`/`PosTree` ABI used by `TraverseSyntaxTree`.

It owns all Epsilon knowledge:

- map each `ruleAlt` to its Epsilon hyper-nonterminal and local alternative;
- fold Gamma's lowered anonymous option/repetition/group nodes into Epsilon's
  logical EAG representation, including Epsilon's special empty alternative;
- omit terminal leaves from Epsilon's heap while preserving required direct
  non-predicate child ordering;
- reconstruct predicate positions from the next real terminal boundary; and
- pass the user-start heap address and existing hyper-arity value to the
  evaluator.

Keep Gamma's parser and tree free of Epsilon types so this module and its
generated projection data can be deleted when Epsilon is retired.

If cheap, add a temporary oracle comparing canonical logical Epsilon trees
from the current LL parser and from `LALR -> ParseTree -> transformation` for
group, option, repetition, and predicate cases.  Do not compare incidental
heap addresses.

Checkpoint:

```sh
dub build
dub test
dub test --config=example
```

### 8. Enable LALR evaluator execution

Use the transformation result to invoke the selected single-sweep or SOAG
evaluator on error-free input.  Reject `--lalr --slag`; preserve LL as the
default and retain its current behavior.  Do not run `ELL1Gen.Test` for this
backend; preserve the single-sweep-then-SOAG evaluator selection order.

Checkpoint:

```sh
dub build
dub test
dub test --config=example
```

### 9. Add focused LALR regression coverage

Do not double every expensive generated-compiler fixture.  Add a small
LL/LALR equivalence subset covering one single-sweep compiler, one SOAG
compiler, EBNF, predicates, output, and checked diagnostic positions.  Use
the existing static-foreach style with this support matrix:

| Parser | Evaluators |
| --- | --- |
| LL (default) | SLAG, single-sweep, SOAG |
| LALR (`--lalr`) | single-sweep, SOAG |

Add canonical `example/` grammars accepted by LALR but rejected by LL(1).
They prove the backend's added value and verify the ELL(1) gate is bypassed.

Checkpoint:

```sh
dub build
dub test
dub test --config=example
```

### 10. Decide permanent table packaging with a spike

After tree and bridge metadata are real, compare one real table embedded as:

1. generated D source with compact immutable array initializers; and
2. one imported text resource processed at compile time into compact arrays.

Judge generated-code clarity, compile time, startup time, and ability to carry
all parser/projection data without extra files.  Then replace runtime JSON
parsing and reconstructed `gamma.grammar` objects with compact table records.
The generated compiler must be self-contained in either case.  JSON may
remain a developer/debug export.

Checkpoint:

```sh
dub build
dub test
dub test --config=example
```

## Future TODO

Consider making LALR the default parser only after all of these conditions
hold:

- the focused LL/LALR equivalence subset agrees on output and checked error
  positions;
- LALR-only examples compile and run;
- recovery trees are implemented and tested;
- a broader one-time audit of existing non-SLAG generated-compiler fixtures
  finds no semantic regression; and
- representative generation, generated-compiler build, and generated-runtime
  performance are not materially worse without a documented reason.

## Required final verification

Every implementation step must leave the repository compiling and all tests
passing.  The primary regression check before committing is:

```sh
dub test --config=example
```

Run the complete verification set at each checkpoint and before handoff:

```sh
dub build
dub test
dub test --config=example
dub run dscanner -- --styleCheck src test
```

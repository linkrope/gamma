# LALR Parse Tree and Epsilon Evaluator Bridge

## Goal

Add LALR as an alternative parser backend for generated compilers while
retaining Epsilon's single-sweep and SOAG evaluator generators during the
incremental Gamma/Epsilon migration.

The target runtime pipeline is:

```text
generated lexer -> table-driven LALR parser -> Gamma ParseTree
                -> removable Gamma-to-Epsilon transformation
                -> Epsilon syntax-tree heap -> generated evaluator
```

SLAG is deliberately excluded.  Its generated evaluator runs in lock-step
with an ELL parser, so it cannot consume a completed LALR parse tree.

The current `--lalr` mode only writes `parser-tables.json` and returns.  It
does not yet build a generated compiler, parse input, or invoke an evaluator.

## Design decisions

- `--lalr` selects the LALR backend.  It bypasses the ELL(1) suitability
  check and is incompatible with `--slag`.
- LALR initially supports the existing single-sweep and SOAG evaluators.
  Their preferred-selection order remains single-sweep, then SOAG.
- The LALR runtime owns a Gamma parse tree.  It must not contain Epsilon
  identifiers, evaluator heap addresses, or predicate nodes.
- The tree is rooted at the user's grammar start symbol.  The parser's
  augmented `(Start)` rule and EOF terminal are parsing machinery only and
  are not tree nodes.
- `ParseTree` carries the root and final lexer `Position`.  The latter is the
  EOF cursor position needed by a later transformation for trailing
  predicates.
- Use the project's existing start-only `io.Position` type.  A synthetic
  terminal inserted during repair has `UndefPos`.
- Define the tree as a recursive `std.sumtype.SumType` with distinct
  `Terminal` and `Rule` alternatives.  Rule children use `This*[]` (or an
  equivalent recursive indirection).  Do not add a Java-style visitor
  hierarchy or extend the unused `gamma.runtime.Node` interface.
- A terminal holds its parser-table terminal ID, position, and synthetic
  status.  A rule holds its stable parser-table `ruleAlt` ID, position, and
  ordered children.  Shifts create terminals; reductions create rules.
- `ParseTree.toString` emits a deterministic GraphViz `digraph` for
  debugging.  Inner nodes are labelled with their LHS nonterminal name;
  terminal leaves use their terminal representation.  The output must not
  contain pointer addresses.
- Existing generated Epsilon lexers remain unchanged.  A small generated
  scanner wrapper delegates to `S.Get(Tok)`, exposes `S.Pos`, and maps Epsilon
  lexer token IDs to compact LALR table terminal IDs.
- Epsilon's bridge is separate and removable.  It transforms a completed
  Gamma tree into Epsilon's existing `Tree`/`PosTree` evaluator ABI; it does
  not make the LALR parser directly construct Epsilon heap records.
- Predicates are filtered out of the parser grammar and remain absent from
  the Gamma tree.  The transformation assigns a predicate the next visible
  terminal position in source order, or `ParseTree.endPosition` at end of
  input.  Consecutive predicates receive the same position.
- The EBNF converter preserves anonymous nonterminal objects, but
  `ParserGrammarBuilder` clones parser symbols and changes their compact IDs.
  Capture an explicit cloned-parser-alternative -> source
  `plainHyperGrammar`-alternative map at that boundary.  Use it to generate
  the later `ruleAlt` projection table.  Do not reverse-map by names or infer
  EBNF structure from arbitrary BNF shape.
- Options and repetitions need explicit bridge coverage.  Gamma lowers them
  to anonymous BNF nonterminals; Epsilon represents `Opt` and `Rep` as
  special logical rules with a distinguished empty alternative.

## Implementation plan

### 1. Introduce the parser-tree runtime model

Add a focused LALR runtime module for `ParseTree`, its recursive `SumType`
node types, and GraphViz rendering.  Keep this separate from
`gamma.grammar.Node`, which represents grammar-definition nodes rather than
parsed input.

Define ownership and invariants clearly:

- terminal and rule nodes are distinct sum-type cases;
- a nonempty rule takes the first child position;
- an empty rule takes the current lookahead position;
- child order follows the parser grammar RHS exactly;
- `ParseTree.root` is the user start-symbol rule; and
- `ParseTree.endPosition` is the lexer position at parser halt.

Add unit tests for node construction and deterministic DOT output.  The DOT
test may be removed later, but concise tests for the permanent tree invariants
must remain.

Checkpoint:

```sh
dub build
dub test
dub test --config=example
```

### 2. Make `LR1Parser` construct trees for valid input

Extend `gamma.parsgen.lalr1.run.LR1Parser` with a semantic stack parallel to
its LR state stack.

- On shift, push a `Terminal` node using the scanner's current `Position`.
- On reduce, pop exactly the RHS number of semantic values, preserve their
  left-to-right order, create a `Rule` node using the stable `ruleAlt` ID,
  and push it.
- On halt, discard the synthetic EOF value and return the user-start node,
  not an augmented-start wrapper.
- Repair the existing `ParserStack.pop` contract before relying on it in
  debug builds.
- Preserve enough table metadata to resolve `ruleAlt` IDs and terminal IDs
  for GraphViz labels.

Add a small, temporary integration fixture using the current table
writer/reader and a test scanner.  It should parse a representative grammar
and print/assert a useful GraphViz tree.  This fixture is a debugging aid and
can be retired once end-to-end LALR evaluator coverage exists.

Checkpoint:

```sh
dub build
dub test
dub test --config=example
```

### 3. Integrate the existing lexer without changing it

Provide a generated wrapper around the existing generated Epsilon lexer.  It
must call `S.Get(Tok)`, expose `S.Pos`, translate lexer tokens into LALR table
terminal IDs, and map lexer EOF to the LALR table's `(end)` terminal.

Do not assume token IDs already agree: parser grammar construction rebuilds
symbols into a compact ID range.  Generate the translation from the grammar
data used to produce the LALR table.

For this intermediate milestone, generate/build a compiler that parses with
the embedded or otherwise available current table representation and prints
`ParseTree.toString` to standard output.  Do not generate or invoke an
Epsilon evaluator yet.

Checkpoint:

```sh
dub build
dub test
dub test --config=example
```

### 4. Add recovery-tree construction

Keep normal-input tree construction separate from recovery initially.  Then
teach the LR repair simulation to maintain/replay semantic values alongside
its state stack.

- Mark inserted terminals synthetic and assign `UndefPos`.
- Return a best-effort `ParseTree` and an error count when recovery reaches a
  halt.
- Do not run the Epsilon transformation or evaluator when the error count is
  nonzero.
- Add focused recovery tests before enabling any evaluator path for repaired
  input.

Checkpoint:

```sh
dub build
dub test
dub test --config=example
```

### 5. Preserve parser-to-source provenance

Refactor `ParserGrammarBuilder.toExtendedParserGrammar` to return a result
containing both the cloned parser grammar and a mapping from every cloned
parser alternative to its source `plainHyperGrammar` alternative.  Retain the
existing compact parser symbol IDs for table size; do not attempt to preserve
source IDs in parser tables.

At table emission, turn this into a stable `ruleAlt`-keyed projection source
for generated compilers.  The source alternative identity connects anonymous
BNF nodes back to their EBNF option/repetition/group occurrence and to the
Epsilon EAG model.

Checkpoint:

```sh
dub build
dub test
dub test --config=example
```

### 6. Build the removable Gamma-to-Epsilon transformation

Implement a separate generated transformation module that consumes a complete
Gamma `ParseTree` and writes the existing Epsilon `Tree` and `PosTree` layout
expected by `TraverseSyntaxTree`.

The module owns all Epsilon-specific knowledge:

- map each `ruleAlt` to its Epsilon hyper-nonterminal and local alternative;
- fold Gamma's lowered anonymous option/repetition/group nodes into Epsilon's
  logical EAG representation, including Epsilon's special empty alternative;
- omit terminal leaves from Epsilon's heap while preserving required direct
  non-predicate child ordering;
- reconstruct predicate positions from the next real terminal boundary; and
- pass the user-start heap address and existing hyper-arity value to the
  evaluator.

Keep Gamma's parser and tree free of Epsilon types so this entire module and
its generated projection data can be deleted when Epsilon is retired.

Before relying only on evaluator output, add a small, time-boxed comparison
fixture for option, repetition, group, and predicate cases.  Compare the
canonical logical Epsilon tree produced by the LL path against the tree
produced by `LALR -> Gamma ParseTree -> transformation`; do not compare raw
heap addresses.  Remove this oracle if it becomes disproportionate once
end-to-end tests give equivalent coverage.

Checkpoint:

```sh
dub build
dub test
dub test --config=example
```

### 7. Wire backend selection into compiler generation

Change `gamma.main` so `--lalr` selects parser generation rather than causing
an early return after writing a table.

- Do not run `ELL1Gen.Test` for the LALR path.
- Reject `--lalr --slag` with a clear diagnostic.
- For LALR, retain the current evaluator selection order: single-sweep first,
  SOAG second.
- Initially, after the parser-tree milestone and before step 6, use the LALR
  compiler only to print DOT.  After step 6, call the transformation and then
  the selected evaluator when parsing has no errors.

Checkpoint:

```sh
dub build
dub test
dub test --config=example
```

### 8. Add focused backend regression coverage

Do not double every expensive generated-compiler fixture.  Add a small
LL/LALR equivalence subset for representative non-SLAG grammars:

- at least one single-sweep compiler;
- at least one SOAG compiler;
- EBNF and predicate-position coverage; and
- matching compiler output and checked diagnostics.

Use `static foreach` or equivalent data-driven cases with these supported
pairs:

| Parser | Supported evaluators |
| --- | --- |
| LL (default) | SLAG, single-sweep, SOAG |
| LALR (`--lalr`) | single-sweep, SOAG |

Add canonical `example/` grammars that are accepted by LALR but fail the
LL(1) suitability check.  They demonstrate the purpose of the new backend and
ensure the LALR route bypasses the ELL(1) gate.

Checkpoint:

```sh
dub build
dub test
dub test --config=example
```

### 9. Choose the generated-table representation with a spike

Do not decide the permanent table packaging before the parser-tree and bridge
metadata are real.  Build a small comparison using one real parser table and
all required projection data:

1. generated D source with compact immutable array initializers; and
2. one imported text resource processed at compile time into compact arrays.

Evaluate generated-code clarity, compile time, executable startup time, and
the ease of carrying all parser/projection metadata without extra sidecar
mapping files.  The generated compiler must be self-contained in either
case.

Use the result to replace runtime JSON parsing and reconstructed
`gamma.grammar` objects with compact table records consumed directly by the
LALR runtime.  Keep JSON only as an optional developer/debug export if it
remains useful.

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

## Required verification

Every implementation step above must leave the repository compiling and all
tests passing.  The primary regression check before committing is:

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

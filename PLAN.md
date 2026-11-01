# Generated lexical parser plan

## Objective

Generate a standalone, longest-match lexer from an Extended Affix Grammar
(EAG). It recognizes quoted terminals and starred hyper-nonterminals before a
generated LALR parser runs.

Plain `--lalr` uses this lexer. `--lalr --p` keeps the existing
primitive-token behaviour: starred hyper-nonterminals remain parser
productions rather than lexer tokens.

The lexer is a module with one interface:

```text
nextToken() -> Token | end | lexical error
```

A `Token` identifies one source-level terminal, has the existing Gamma `Position`
at which it begins, and, for a starred hyper-nonterminal, contains its
completed Gamma `RuleNode` derivation. A consuming parser maps this source-level
identity to its own token domain. The lexer contains no Epsilon heap addresses,
evaluator code, or outer-parser state. There is no lexical span type: `Position`
is the position representation throughout Gamma.

## Design decisions

### Use one combined lexical grammar

Generate one lexical grammar, not one parser per starred nonterminal. It has
an implementation-only root equivalent to:

```text
(TokenStart) -> Candidate (token-end)
```

`Candidate` ranges over every quoted terminal used by the parser grammar and
every starred hyper-nonterminal. `(token-end)` is virtual: it is never read
from source and is distinct from actual file EOF.

Quoted terminals are lowered to input characters, not treated as already
separated source tokens. Therefore one lexer can resolve both:

```text
"<" versus "<="
"if" versus id* = letter | id letter
```

### Longest match is independent of parsing

The lexer advances through source characters and records every prefix that
would accept with virtual `(token-end)`. It commits the latest accepted
prefix when no candidate can continue or when `WhiteSpace` establishes a boundary.
The virtual marker is a prefix-membership query, not a source boundary.

The initial implementation may snapshot a lexical LR configuration and apply
only virtual-end reductions. It must not restart parsing from the beginning
of the token for each character, and it must not use error repair. Benchmark
this mechanism; later optimization must not change its contract.

Choose a result as follows:

1. Prefer the candidate consuming the most source characters.
2. On equal length, prefer a quoted-terminal candidate over a starred
   hyper-nonterminal candidate.  Candidate and rule declaration order has no
   effect.
3. If two distinct candidates of the same kind still tie, reject the lexical
   grammar as ambiguous.  For multiple derivations of the selected candidate,
   use a documented,
   deterministic alternative-order policy or reject the grammar. Never depend
   on table or hash iteration order.

### Require a deterministic lexical grammar initially

The generated lexical grammar must be LALR. Its lexical conflict policy is:

- shift while a longer candidate remains possible;
- on virtual end, resolve an equal-length terminal/starred-rule conflict in
  favour of the terminal, and report every remaining candidate conflict;
- report all other unresolved conflicts as lexical-grammar generation errors.

This accepts natural left-recursive definitions such as `id` and leaves room
for recursive lexical definitions such as nested comments, without taking on
generalized LR parsing in the first version. Initial comment handling remains
hardcoded as described below.

### Preserve lexical derivations

An ordinary quoted-terminal token supplies a terminal leaf. A starred token
supplies the complete `RuleNode` tree made by the lexical parser: original
Gamma nonterminal IDs, one-based local alternative ordinals, ordered children,
and `Position` values.

This is required for evaluation. Literal leaves may be omitted by a tree
bridge, but a starred rule tree contains the derivation that computes the
rule's affix values. An opaque token ID is not sufficient.

The outer LALR parser uses the token identity to choose its shift action. On
a starred token it pushes the supplied tree, rather than creating a terminal
leaf. This keeps the outer parser free of Epsilon types.

### No lexical repair

A dead lexical configuration means only that a candidate cannot consume the
next character. If no accepted prefix exists at a source position, emit one
lexical diagnostic there, make documented forward progress, and prevent
evaluation. Parser repair belongs only to the outer syntax parser.

### Initial `WhiteSpace` policy

The first implementation retains the established hardcoded rules:

- Unicode whitespace separates and is skipped between tokens.
- `(* ... *)` comments are skipped and may nest.
- Whitespace is not silently accepted inside an ordinary starred token.

The EAG surface syntax reserves leading-`:` `WhiteSpaceRule` definitions. A
later step must retain and analyze them, then replace the hardcoded
`WhiteSpace` logic with generated whitespace/comment rules. The outer parser
must never be responsible for `WhiteSpace`.

## Architecture

```text
EAG
 │
 ├── lexical-grammar projection ──> lexical LALR tables
 │                                      │
 │ source characters ───────────────────┤
 │                                      ▼
 │                                  Token
 │                                      │
 └── parser-grammar projection ──> parser-specific token adapter
                                        │
                                        ▼
                              generated LALR or ELL parser
```

The lexical projection lowers quoted terminals to Unicode character sequences,
retains source rule/alternative provenance, creates the combined root, and
records each candidate's source identity and kind. The outer-parser projection
is separate.

In plain `--lalr`, starred occurrences become parser terminals. In
`--lalr --p`, they remain parser productions and the established primitive
lexer path is unchanged.

## Implementation steps

- [x] 1. Make hardcoded `WhiteSpace` a working lexer — `dub test` passes its
  Unicode-whitespace, nested-comment, EOF, and unterminated-comment checks.
- [x] 2. Generate and run a terminal-only LALR lexer — generated LALR
  compilers trace terminal-only acceptance through a parallel lexical runner.
- [ ] 3. Add starred rules to the generated lexer — the canonical
  left-recursive identifier fixture passes its generated-compiler trace test.
- [ ] 4. Connect plain LALR parsing — generated compiler/evaluator tests pass.
- [ ] 5. Add diagnostics and tracing — focused generated-compiler diagnostic
  tests pass.
- [ ] 6. Evaluate reuse by ELL-generated compilers — shared-fixture
  equivalence tests establish whether the adapter is viable.
- [ ] 7. Generate `WhiteSpace` from `WhiteSpaceRule` — custom-`WhiteSpace`
  tests pass.
- [ ] 8. Broaden regression coverage and measure cost — the full validation
  suite passes and benchmark results are recorded.

### 1. Make hardcoded `WhiteSpace` a working lexer

Add `gamma.runtime.lr.LR1Lexer`, a Gamma-only lexer whose first implementation
advances through Unicode `WhiteSpace` and nested `(* ... *)` comments. It
is an input range: `empty` means end of input, `front` returns the next
non-`WhiteSpace` `dchar`, and `popFront` advances to the following one. Its
`position` is the existing `Position` of `front`. It reports an unterminated
comment. It does not yet recognize grammar tokens.

Use focused unit tests as its smoke-test harness: prove that it skips leading,
inter-token, and trailing `WhiteSpace`, then reaches EOF. This is the first
working milestone; it has no LALR tables, parser, token model, or evaluator.
The terminal-only milestone changes this same range's element type from
`dchar` to source-level `Token`; there is no disposable pre-lexer.

### 2. Generate and run a terminal-only LALR lexer

Add Gamma-only `Token` and lexical-error types now that the `Lexer` has a
consumer. A result distinguishes a quoted terminal, end of input, and a
reported failure. Every diagnostic and token location uses the existing
`Position`; do not introduce a span type. Token identities remain original
Gamma symbols, never compact table IDs.

Project only quoted terminals into a combined lexical grammar and add the
generated root and virtual end-of-token marker. Lower terminals to Unicode
characters and reject lexical conflicts that are not resolved by longest
match. Preserve source provenance and original identities.

Reuse `PennelloDeRemer`, the LALR table records, and the table writer to
generate terminal-only tables. Add a no-repair lexical LR runner separate from
the error-correcting `LR1Parser`; it may share action records and reduction
helpers, but never recovery. It buffers Unicode input, tests virtual-end
acceptance without consuming source, records the furthest accepted terminal,
and rewinds any over-read characters before the next token.

Generate the lexical tables into the normal LALR compiler. Its legacy lexer
remains the parser input; a second `LR1Lexer` consumes a copied `Input` in
parallel and emits deterministic terminal identities and their `Position`
values under `--verbose`. Prove `<` versus `<=`, adjacent terminals,
hardcoded `WhiteSpace`, and EOF immediately after a terminal. There is still
no starred rule, outer parser handoff, tree bridge, or evaluator use of the
new lexer.

### 3. Add starred rules to the generated lexer

Extend the projection and lexical LR runner with starred hyper-nonterminal
candidates and the helper rules they require. A starred result retains its
complete Gamma `RuleNode`; a literal result has no rule root. Reject nullable
starred tokens and lexical conflicts that remain after the stated precedence.

The canonical fixture is `example/lr-lexer-test.eag`; its exact input
and expected token identities are backtick strings beside its regression test
in `test/lr_lexer.d`. Its `id` rule is directly left-recursive
in both the meta and hyper grammar. It proves that LALR lexing, rather than a
regular-expression shortcut, handles the identifier recursion. It also
establishes terminal-over-starred precedence for `if` and `id*`, and
longest-match precedence for `ifx`.

Extend the generated compiler's lexical trace to print deterministic
starred-rule trees. Test left-recursive identifiers, keyword/identifier
precedence, failed prefixes, and nested-comment `WhiteSpace`. Verify that no
recovery action is available.

### 4. Connect plain LALR parsing

Make parser-grammar projection mode-dependent:

- plain `--lalr` omits starred lexical-rule productions and projects their
  occurrences to parser terminals;
- `--lalr --p` preserves the established primitive-token parser grammar and
  lexer behaviour.

Replace the existing `gamma.runtime.Lexer` handoff, which can return only an
`int` token ID and a `Position`. The replacement handoff carries the compact
LALR terminal ID, `Position`, and an optional supplied parse tree. On SHIFT,
`LR1Parser` pushes the supplied starred-rule tree; for a quoted terminal it
creates the usual terminal leaf. This is required to preserve a lexical
derivation through the outer parser's tree stack.

Generate the source-level-token-to-compact-terminal adapter for plain
`--lalr`. Its result must retain the supplied tree instead of reducing it to
an `int`. Update `--lalr --p` to use the replacement handoff as well, while
keeping its established primitive-token behaviour.

Run generated compilers with evaluators. Verify that an identifier affix still
receives the same value through its lexical derivation, and that evaluation
does not run after a lexical error.

### 5. Add diagnostics and tracing

Report lexical errors at the beginning of the unrecognized input using
`Position`. Keep them separate from outer syntax-error recovery messages.

Verbose tracing should reveal emitted tokens, their `Position`, selected
precedence, and lexical trees without printing addresses. Add generated-
compiler tests for invalid characters, unterminated hardcoded comments,
invalid token prefixes, and line/column positions.

### 6. Evaluate reuse by ELL-generated compilers

The lexical result is source-level rather than LALR-table-specific, so an ELL
adapter is possible. Investigate an optional ELL mode that consumes the same
generated lexical stream instead of its parser-state-dependent lexer.

It must map token identities to the ELL token domain, preserve starred-rule
derivations for ELL evaluation, retain legacy ELL behaviour until equivalence
tests pass, and prove matching output and checked diagnostics on a small
shared fixture set.

ELL reuse is not a prerequisite for plain LALR lexing. It is an adapter made
possible by the lexer seam, not a reason to couple the parser runtimes.

### 7. Generate `WhiteSpace` from `WhiteSpaceRule`

Extend EAG analysis so `WhiteSpaceRule` definitions are retained as analyzed
grammar data rather than skipped. Specify separator/comment roles, priority,
and nesting semantics.

Generate `WhiteSpace` recognition from those definitions, replacing the
initial hardcoded whitespace/comment logic. Preserve the lexical interface and
the rule that `WhiteSpace` terminates ordinary tokens unless a defined lexical
rule explicitly consumes it.

Test custom separators, comments, nesting, adjacency to tokens, and malformed
`WhiteSpace`.

### 8. Broaden regression coverage and measure cost

Add focused coverage for:

| Parser | Lexer mode | Evaluators |
| --- | --- | --- |
| ELL | legacy lexer | SLAG, single-sweep, SOAG |
| LALR | generated lexical parser | single-sweep, SOAG |
| LALR | `--p` primitive path | single-sweep, SOAG |
| ELL, if implemented | generated lexical parser | supported ELL evaluators |

Cover EBNF, predicates, lexical derivations, output, checked diagnostics,
overlapping literals, keyword/identifier precedence, and LALR-only grammars.

Measure generation time, generated-compiler build time, runtime speed, and
memory use. Optimize virtual-end checkpoints or buffering only after a
measured regression.

## Non-goals for the first implementation

- Do not let outer-parser state affect lexical choices.
- Do not implement lexical error repair.
- Do not add Epsilon types or evaluator state to the lexical runtime.
- Do not implement generalized LR parsing; reject unsupported lexical
  conflicts precisely.
- Do not replace `--lalr --p` before plain `--lalr` is proven.
- Remove `gamma.runtime.Lexer` and the legacy generated `GeneratedLexer` once
  both plain `--lalr` and `--lalr --p` use the replacement tree-carrying
  handoff.
- Do not replace hardcoded `WhiteSpace` before `WhiteSpaceRule` semantics are
  analyzed and tested.

## Validation

Run step-specific tests after each step. Before merging lexical-parser work,
run the complete verification set:

```sh
dub build
dub test
dub test --config=example
dub run dscanner -- --styleCheck src test
```

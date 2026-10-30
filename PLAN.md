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

A `Token` identifies one source-level terminal, has start and end positions,
and, for a starred hyper-nonterminal, contains its completed Gamma `RuleNode`
derivation. A consuming parser maps this source-level identity to its own
token domain. The lexer contains no Epsilon heap addresses, evaluator code,
or outer-parser state.

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
prefix when no candidate can continue or when trivia establishes a boundary.
The virtual marker is a prefix-membership query, not a source boundary.

The initial implementation may snapshot a lexical LR configuration and apply
only virtual-end reductions. It must not restart parsing from the beginning
of the token for each character, and it must not use error repair. Benchmark
this mechanism; later optimization must not change its contract.

Choose a result as follows:

1. Prefer the candidate consuming the most source characters.
2. On equal length, prefer the candidate declared earlier in source order.
3. For multiple derivations of the selected candidate, use a documented,
   deterministic alternative-order policy or reject the grammar. Never depend
   on table or hash iteration order.

### Require a deterministic lexical grammar initially

The generated lexical grammar must be LALR. Its lexical conflict policy is:

- shift while a longer candidate remains possible;
- on virtual end, resolve equal-length candidate conflicts by declared source
  priority;
- report all other unresolved conflicts as lexical-grammar generation errors.

This accepts natural left-recursive definitions such as `id` and leaves room
for recursive lexical definitions such as nested comments, without taking on
generalized LR parsing in the first version. Initial comment handling remains
hardcoded as described below.

### Preserve lexical derivations

An ordinary quoted-terminal token supplies a terminal leaf. A starred token
supplies the complete `RuleNode` tree made by the lexical parser: original
Gamma nonterminal IDs, one-based local alternative ordinals, ordered children,
and source positions.

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

### Initial trivia policy

The first implementation retains the established hardcoded rules:

- Unicode whitespace separates and is skipped between tokens.
- `(* ... *)` comments are skipped and may nest.
- Whitespace is not silently accepted inside an ordinary starred token.

The EAG surface syntax reserves leading-`:` `WhiteSpaceRule` definitions. A
later step must retain and analyze them, then replace the hardcoded trivia
logic with generated whitespace/comment rules. The outer parser must never
be responsible for trivia.

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
records candidate source order. The outer-parser projection is separate.

In plain `--lalr`, starred occurrences become parser terminals. In
`--lalr --p`, they remain parser productions and the established primitive
lexer path is unchanged.

## Implementation steps

### 1. Specify the lexical-only vertical slice

Create one canonical grammar and checked expected token sequence covering,
in one run:

- direct terminals including `<` and `<=`;
- a left-recursive starred identifier;
- a keyword that also belongs to the identifier language;
- adjacent tokens, leading/trailing whitespace, and hardcoded nested
  comments; and
- EOF directly after a token.

The generated lex-only runner arrives in step 5. Its contract is fixed here:
it reads source, writes a deterministic sequence of token identities and
spans, and may print a deterministic tree for starred tokens. It must not
invoke an outer parser or evaluator.

### 2. Define source-level lexical data

Add Gamma-only runtime types for `Token`, source spans, and lexical errors.
The types distinguish quoted terminals, starred rules with a `RuleNode`
derivation, end of input, and a reported lexical failure.

Use original Gamma symbol identities here, never compact LALR table IDs. Add
unit tests for spans, ownership, and the invariant that a starred result has a
rule root while a literal result does not.

### 3. Build the lexical grammar projection

Project analyzed EAG data into one lexical grammar.

- Lower quoted terminals to their Unicode character sequences.
- Include each starred hyper-nonterminal and required lexical helper rules.
- Add the generated root and virtual end-of-token marker.
- Preserve source order, local alternative ordinals, and original IDs.
- Record candidate source priority.
- Reject nullable starred tokens and unsupported lexical conflicts.

Add generator tests for shared prefixes (`<`/`<=`) and keyword/identifier
overlap. Ensure neither candidate is lost before priority is applied.

### 4. Implement the no-repair lexical LR runtime

Add a lexical recognizer separate from the error-correcting outer `LR1Parser`.
It may share table records and tree reduction helpers, but its observable
behaviour is distinct.

It must:

- consume buffered Unicode source characters;
- maintain the live lexical LR configuration;
- test virtual-end acceptance without consuming source;
- retain the furthest accepted token and its tree;
- retain or rewind over-read input before beginning the next token;
- enforce longest-match and source-priority selection; and
- report failure without inserting, deleting, or synthesizing input.

Unit-test left-recursive identifiers, overlapping operators,
keyword-versus-identifier precedence, failed prefixes, and nested-comment
trivia. Verify that no recovery action is available.

### 5. Generate and run the standalone lexer

Generate a lexical table module and the lex-only executable from steps 1–4.
Make the lexical-only acceptance tests pass. Inspect emitted tokens and
starred-rule trees. There is still no outer parser, tree bridge, or evaluator
in this milestone.

### 6. Connect plain LALR parsing

Make parser-grammar projection mode-dependent:

- plain `--lalr` omits starred lexical-rule productions and projects their
  occurrences to parser terminals;
- `--lalr --p` preserves the established primitive-token parser grammar and
  lexer behaviour.

Generate an adapter from source-level tokens to compact LALR table terminals.
Extend the parser/lexer handoff so a shift pushes a supplied starred-rule tree
and otherwise creates the usual terminal leaf.

Run generated compilers with evaluators. Verify that an identifier affix still
receives the same value through its lexical derivation, and that evaluation
does not run after a lexical error.

### 7. Add diagnostics and tracing

Report lexical errors at the beginning of the unrecognized input. Keep them
separate from outer syntax-error recovery messages.

Verbose tracing should reveal emitted tokens, spans, selected priorities, and
lexical trees without printing addresses. Add generated-compiler tests for
invalid characters, unterminated hardcoded comments, invalid token prefixes,
and line/column positions.

### 8. Evaluate reuse by ELL-generated compilers

The lexical result is source-level rather than LALR-table-specific, so an ELL
adapter is possible. Investigate an optional ELL mode that consumes the same
generated lexical stream instead of its parser-state-dependent scanner.

It must map token identities to the ELL token domain, preserve starred-rule
derivations for ELL evaluation, retain legacy ELL behaviour until equivalence
tests pass, and prove matching output and checked diagnostics on a small
shared fixture set.

ELL reuse is not a prerequisite for plain LALR lexing. It is an adapter made
possible by the lexer seam, not a reason to couple the parser runtimes.

### 9. Generate trivia from `WhiteSpaceRule`

Extend EAG analysis so `WhiteSpaceRule` definitions are retained as analyzed
grammar data rather than skipped. Specify separator/comment roles, priority,
and nesting semantics.

Generate trivia recognition from those definitions, replacing the initial
hardcoded whitespace/comment logic. Preserve the lexical interface and the
rule that trivia terminates ordinary tokens unless a defined lexical rule
explicitly consumes it.

Test custom separators, comments, nesting, adjacency to tokens, and malformed
trivia.

### 10. Broaden regression coverage and measure cost

Add focused coverage for:

| Parser | Lexer mode | Evaluators |
| --- | --- | --- |
| ELL | legacy scanner | SLAG, single-sweep, SOAG |
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
- Do not replace hardcoded trivia before `WhiteSpaceRule` semantics are
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

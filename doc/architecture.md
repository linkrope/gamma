# Architecture

Gamma is a hybrid compiler generator mid-migration: new Gamma modules own parsing, validation, and grammar work, while legacy Epsilon modules still generate and evaluate most compiled compilers.

```text
.eag specification
  │
  ├─ Gamma front end: lex / parse / validate
  │    ├─ meta grammar: describes affix values
  │    └─ hyper grammar: recognizes input and threads affixes
  │
  ├─ Gamma object model + EBNF lowering
  │
  ├─ EAGBuilder compatibility bridge
  │
  ├─ Epsilon evaluator selection
  │    ├─ SLAG: direct one-pass evaluation
  │    ├─ Sweep: parse tree + scheduled evaluation
  │    └─ SOAG: general visit-sequence evaluation
  │
  └─ generated D source + generated compiler
```

The orchestration is [main.d](../src/gamma/main.d#L148). It analyzes a grammar, converts it to `epsilon.EAG`, selects a backend, writes generated D plus a standalone `dub.json`, and builds unless `--generate` is passed.

## What an EAG is

The input language has two coupled grammars:

- Meta grammar (`=`): defines valid values carried as affixes.
- Hyper grammar (`:`): recognizes subject input and passes those affix values through rules.

For example, `example/abc.eag` uses a meta grammar to build a sequence of `'1'` values while its hyper grammar recognizes matching runs of `a`, `b`, and `c`. The start symbol must expose exactly one output affix, which the analyzer enforces in [analyzer.d](../src/gamma/input/epsilang/analyzer.d#L121).

## Main module areas

| Area | Purpose |
|---|---|
| `src/gamma/input/epsilang/` | Hand-written lexer and recursive-descent parser for `.eag` |
| `src/gamma/grammar/` | Core indexed CFG model and fixed-point analyses |
| `src/gamma/grammar/hyper/` | Affixes, signatures, EBNF nodes, semantic checks |
| `src/gamma/input/earley/` | Parses affix forms against the meta grammar |
| `src/gamma/input/EAGBuilder.d` | Translates Gamma’s model into legacy Epsilon IR |
| `src/gamma/parsgen/lalr1/` | Experimental LALR lexer/parser generation |
| `src/epsilon/` | Mature LL(1) generator and evaluator backends |
| `src/gamma/runtime/` | Runtime support for generated LALR parsers |
| `fix/` | D source templates spliced into generated compilers |
| `example/`, `test/`, `unittest/` | Grammar corpus and regression coverage |

## Gamma’s front end and model

The Epsilang lexer accepts Unicode identifiers, quoted/raw strings, nested comments, and source-position tracking. The parser builds both grammars, supports local recovery for multiple diagnostics, and marks `*` definitions as lexical. Start with [parser.d](../src/gamma/input/epsilang/parser.d#L111).

The plain grammar model is deliberately compact:

- `Grammar`: terminal/nonterminal registries, rules, start symbol.
- `Rule`: alternatives for one LHS.
- `Alternative`: LHS, RHS nodes, source position.
- `GrammarBuilder`: symbol interning and undefined-reference diagnostics.

See [Grammar.d](../src/gamma/grammar/Grammar.d#L9) and [GrammarBuilder.d](../src/gamma/grammar/GrammarBuilder.d#L16).

`GrammarProperties` provides lazy nullability, productivity, reachability, lexicalness, and predicate/strong-nullability analysis. It builds reverse RHS occurrence indexes, then uses worklists rather than repeatedly scanning all productions. [GrammarProperties.d](../src/gamma/grammar/GrammarProperties.d#L20)

## Affixes and hyper grammar

The hyper model adds EAG semantics without complicating the ordinary grammar model:

- `HyperLhsNode` carries a signature and formal parameters.
- `HyperSymbolNode` carries actual parameters.
- `Signature` gives each affix domain and direction (`-` input, `+` output).
- `Variable` captures an affix variable, numeric suffix, and inequality marker.
- `Composite` represents a meta-grammar-derived affix tree.

Parameters are stored indirectly using `Params(key, position)`, indexing side arrays of parsed affix terms. That allows the parser to collect affix forms first and parse them only after the full meta grammar is known. [HyperGrammar.d](../src/gamma/grammar/hyper/HyperGrammar.d#L28)

The Earley implementation is only for parsing those affix forms at compiler-generation time; it is not the generated language parser. It reconstructs `Variable`/`Composite` trees from Earley item links. [earley/Parser.d](../src/gamma/input/earley/Parser.d#L54)

`HyperGrammar` validates consistent signatures, required actual parameters, and affix-variable dataflow. It checks that each variable is defined according to parameter direction and that `!x` has a corresponding `x`. [HyperGrammar.d](../src/gamma/grammar/hyper/HyperGrammar.d#L157)

## EBNF support

Groups, options, and repetitions remain explicit AST nodes while parsing so parameter and position information survives. `EBNFConverter` then lowers them to a plain grammar:

- Group → generated helper rule.
- Option → helper rule plus ε alternative.
- Repetition → right-recursive helper plus ε alternative.
- Direct forms such as `S: ( ... ).` avoid a redundant wrapper helper.

The lowered grammar is cached by `plainHyperGrammar`. [EBNFConverter.d](../src/gamma/grammar/hyper/EBNFConverter.d#L22)

## The key migration seam

[EAGBuilder.d](../src/gamma/input/EAGBuilder.d#L32) converts Gamma’s validated object graph into Epsilon’s compact, index-based IR in four ordered passes:

1. Meta grammar records.
2. Hyper grammar’s linked alternatives/factors and EBNF structures.
3. Signatures, parameters, affix trees, and scoped variable records.
4. Reachability/productivity/nullability bit sets.

This is a semantic conversion, not simple serialization: affix direction determines whether an occurrence defines or uses a value. [EAGBuilder.d](../src/gamma/input/EAGBuilder.d#L454)

## Epsilon’s generator backends

`epsilon.EAG` is a compact mutable generator IR, combining linked grammar structures with integer arenas for parameters, trees, variables, and signatures. Much of Epsilon still uses a transitional global instance. [eag.d](../src/epsilon/eag.d#L79)

The default evaluation strategy is:

1. **SLAG** — direct predictive parsing and evaluation when semantic restrictions allow it.
2. **Single sweep** — create a parse tree, topologically schedule semantic work, then evaluate.
3. **SOAG** — general fallback, using partitioned visits for complex dependency graphs.

The LL(1) generator computes FIRST/FOLLOW/director sets, rejects incompatible grammars, creates recovery defaults, emits parser procedures, and generates the lexer. [ell1gen.d](../src/epsilon/ell1gen.d#L349)

Single-sweep evaluation derives an ordering between RHS factors from variable dependencies. [sweep.d](../src/epsilon/sweep.d#L272)

SOAG is the most general backend: it derives direct/transitive affix dependencies, selects valid orientations, creates visit sequences, and optionally performs storage/liveness optimization. [soag.d](../src/epsilon/soag/soag.d#L440)

## Experimental LALR path

`--lalr` is active and tested, but still marked experimental. It replaces syntax parsing/lexing while retaining Epsilon evaluation:

```text
plain hyper grammar ──> parser projection ──> LALR tables ──> LR runtime
quoted terminals    ──> character grammar  ──> LALR tables ──> longest-match lexer
                                                     │
                                                     └─ parse-tree bridge ──> Epsilon evaluator
```

The parser projection makes lexical hyper nonterminals terminals, removes predicate nodes from syntactic RHSs, and retains mappings for the evaluator bridge. [ParserGrammarBuilder.d](../src/gamma/parsgen/lalr1/ParserGrammarBuilder.d#L31)

`PennelloDeRemer` computes LALR lookaheads on an LR(0) machine using READ/FOLLOW/lookback relations and SCC propagation. [PennelloDeRemer.d](../src/gamma/parsgen/lalr1/PennelloDeRemer.d#L227)

At runtime, `LR1Lexer` implements longest-match tokenization with whitespace/comment skipping, while `LR1Parser` constructs parse trees and does automatic repair through deletion to anchors and token insertion. [LR1Lexer.d](../src/gamma/runtime/lr/LR1Lexer.d#L69) and [LR1Parser.d](../src/gamma/runtime/lr/LR1Parser.d#L99)

## Current boundaries to keep in mind

- Epsilang whitespace-rule declarations are intentionally unsupported.
- Earley affix parsing keeps one derivation and does not report ambiguity.
- `Parser.getErrorCount` returns placeholder `42` for any error.
- LALR currently ignores lexical `*` token-mark semantics.
- Some legacy error paths still use `assert` placeholders.
- Template-driven Epsilon generation and its global IR are acknowledged migration debt.

For a focused reading route: [main.d](../src/gamma/main.d#L148) → [Epsilang parser](../src/gamma/input/epsilang/parser.d#L111) → [HyperGrammar](../src/gamma/grammar/hyper/HyperGrammar.d#L28) → [EBNFConverter](../src/gamma/grammar/hyper/EBNFConverter.d#L22) → [EAGBuilder](../src/gamma/input/EAGBuilder.d#L32) → the relevant Epsilon backend.

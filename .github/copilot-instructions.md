# gamma — Extended Affix Grammar Compiler Generator

## Build & Test

```sh
dub build                   # build gamma executable
dub run -- example/abc.eag  # run against a grammar file
dub test :unittest          # unit tests (Silly framework)
dub test :example           # integration tests — builds gamma, runs all example/*.eag grammars
dub build --build=release-gamma  # optimised release build
```

The `:example` suite is the primary regression check; run it before committing.

## Architecture

Two source trees that are being progressively merged:

| Directory | Role | Status |
|-----------|------|--------|
| `src/gamma/` | Modern grammar model, LALR(1) gen, Earley parser, EBNF lowering | **Active development** |
| `src/epsilon/` | Complete LL(1)-based pipeline (lexer → analyzer → code generators) | **Legacy; being replaced** |

### Current data flow

1. `src/gamma/input/epsilang/` — EAG spec lexer + parser → builds `gamma.grammar.*` model
2. `src/epsilon/analyzer.d` — authoritative semantic analysis (validates affix forms, builds epsilon globals)
3. `src/epsilon/{ell1gen,lexgen,slaggen,soaggen,...}.d` — code generators

### Ongoing merger plan (`plan-replaceEpsilonAnalyzer.md`)

- **Phase 1** *(in progress)*: wire gamma's Earley parser into the analysis pipeline; attach `Term` trees to the grammar model. Entry point: `src/gamma/input/earley/Parser.d`.
- **Phase 2–4**: audit parser parity → build `EAGBuilder` transformer → swap out `epsilon.analyzer`.

See [plan-replaceEpsilonAnalyzer.md](../plan-replaceEpsilonAnalyzer.md), [TODO.md](../TODO.md), and [WIP.md](../WIP.md) for the detailed roadmap.

## Conventions

### Naming
- Classes/types: `PascalCase`, one class per file, filename matches class name
- Methods and local variables: `camelCase`
- Private fields: `camelCase_` (trailing underscore)
- Module names: lowercase dot-separated packages (e.g. `gamma.grammar.Nonterminal`)

### Code style
- Copyright header: `//          Copyright Mario Kröplin <year>.` + BSL-1.0 boilerplate
- Public APIs: `/** javadoc-style block comments */`
- Visitor pattern is pervasive — new grammar node types must implement `accept(Visitor)`
- Defensive copies in constructors: use `.dup` on arrays
- D `in`-contracts for preconditions (e.g. `in (lexer.front == Token.string_)`)
- **No bare `true`/`false` arguments** — use `std.typecons.Flag` instead. Declare parameters as `Flag!"name"` and pass `Yes!"name"` / `No!"name"` at call sites. `Yes!` and `No!` convert implicitly to `bool`, so the function body needs no changes (see `Variable`'s `Unequal` flag for an example).
- Prefer `.front` over `[0]` for range/array access.
- Use UFCS when the call reads like a sentence (e.g. `5.minutes` over `minutes(5)`).

### Grammar examples
- Canonical examples live in `example/*.eag`; add new ones there for regression coverage
- `fix/epsilon/` holds string-imported patches embedded by code generators at generation time — do not delete

## Key files

- [`src/gamma/main.d`](../src/gamma/main.d) — CLI entry point and pipeline orchestration
- [`src/gamma/grammar/Grammar.d`](../src/gamma/grammar/Grammar.d) — central grammar model
- [`src/gamma/input/earley/Parser.d`](../src/gamma/input/earley/Parser.d) — Earley parser (Phase 1 focus)
- [`src/epsilon/analyzer.d`](../src/epsilon/analyzer.d) — legacy authoritative analyzer
- [`include/runtime.d`](../include/runtime.d) — public API of generated compilers

# gamma — Extended Affix Grammar Compiler Generator

## Build and test

```sh
dub build                                 # build the gamma executable
dub run -- example/abc.eag                # run against a grammar file
dub test                                  # unit tests (Silly framework)
dub test --config=example                 # integration tests; builds gamma first
dub build --build=release-gamma           # optimized release build
dub run dscanner -- --styleCheck src test # style chedk
```

The `:example` suite is the primary regression check; run it before committing.

## Architecture

The `src/gamma/` tree contains the grammar model, input analysis, Earley parser, LALR(1) generator and EBNF lowering. The `src/epsilon/` tree contains the legacy LL(1)-based compiler generation pipeline. Both retain patterns from their source languages; prefer idiomatic D for new code as the trees are merged.

The current pipeline analyzes the input with `gamma.input.epsilang.Analyzer`, converts the result to the epsilon model with `gamma.input.EAGBuilder`, and uses the epsilon generators. See `src/gamma/main.d` for orchestration and `TODO.md` for the roadmap.

## Conventions

- Use `PascalCase` for classes and types and `camelCase` for methods and local variables. Keep one class per file, with a matching filename.
- Use `camelCase` for private fields; add a trailing underscore only to disambiguate a field from a getter or setter.
- Avoid abbreviations in names: use `nonterminal`, `alternative` and `operator`, with exceptions for well-known domain abbreviations such as `lhs`, `rhs` and `eag`.
- Use UFCS liberally.
- Use local imports where possible.
- Avoid `cast` where possible; prefer designs that eliminate runtime casts, such as templates, interfaces or `std.sumtype`.
- Prefer a well-named helper function to a block preceded by an explanatory comment.
- Make defensive copies of constructor arrays with `.dup`.
- Use D `in` contracts for preconditions.
- Avoid bare `true` or `false` arguments: use `std.typecons.Flag` parameters and `Yes` or `No` at call sites.
- Prefer `.front` to `[0]` for range and array access.
- Prefer newspaper style: place a function or type below its last use.
- Write multi-line expected test text as `` `...`.outdent.strip ``.
- Write concise imperative commit messages, such as `Add error handling`.

Canonical grammar examples live in `example/`; add examples there for regression coverage. The files in `fix/` are string-imported patches embedded by the code generators and must be retained.

## Key files

- `src/gamma/main.d` — CLI entry point and pipeline orchestration
- `src/gamma/grammar/Grammar.d` — central grammar model
- `src/gamma/input/earley/Parser.d` — Earley parser
- `src/gamma/input/epsilang/analyzer.d` — input analyzer
- `src/gamma/input/EAGBuilder.d` — conversion to the epsilon model
- `include/runtime.d` — public API of generated compilers

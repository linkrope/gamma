# Coding standards

This is the source of truth for review standards. Read it before changing D code and when reviewing any change.

## D conventions

Use the [D Style](https://dlang.org/dstyle.html) as the baseline and the [D language specification](https://dlang.org/spec/spec.html) for language semantics. These gamma-specific rules take precedence where they are more specific. `dscanner.ini` is the source of truth for mechanically checked style.

Apply these rules to new and substantially changed code in `src/gamma/`. In `src/epsilon/`, preserve the local legacy style unless the change is already a contained modernization.

### Names and layout

- Use `PascalCase` for types and `camelCase` for functions, methods, and locals. Keep one primary type per matching file.
- Use `camelCase` for private fields; add a trailing underscore only when it distinguishes a field from its accessor.
- Spell domain names in full: `nonterminal`, `alternative`, and `operator`. `lhs`, `rhs`, and `eag` are established exceptions.
- Name primitive values by their domain and unit. In particular, an index must say what it indexes, such as `lexicalRootIndex`; introduce a small domain type when the value crosses a module boundary.
- Name mappings for their direction, such as `helpersByTerminal`. Prefer a direct relation or a well-named set over a predicate that scans a mapping to rediscover the relation.
- Prefer a well-named helper to a comment that narrates a block. Use newspaper order: place a function or type below its last use.

### D idioms and boundaries

- Make query methods `const`; bind locals as `const` after their initial assignment. Use `immutable` when transitive immutability is part of the value's contract.
- At an ownership boundary, copy input arrays with `.dup`. Keep owned mutable arrays private: expose a duplicate or a read-only range, never the backing array.
- Use UFCS for transformations and range pipelines when it reads left-to-right; use member calls for an object's primary protocol.
- Prefer `.front` to `[0]` when accessing the first element of a range.
- Prefer `.empty` to `.length == 0` or `.length != 0` when checking whether a range has elements.
- Keep imports sorted. Use a selective local import (`import module : name;`) in the narrowest scope that needs it; keep shared dependencies at module scope.
- Model alternatives with polymorphism, templates, interfaces, or `std.sumtype` before reaching for `cast`. A remaining cast must immediately establish its invariant: bind and validate the outer node before casting its payload.
- Initialize mutable locals explicitly. Represent boolean modes with a `std.typecons.Flag` parameter and `Yes` or `No`, rather than a bare boolean argument.
- Keep correlated metadata together at module boundaries. When the same group of fields repeatedly crosses a boundary, introduce a focused metadata type.

### Invariants, diagnostics, and tests

- State internal programmer preconditions with `in` contracts; use `assert` for invariants that follow from this module's own logic.
- Report malformed user input through the existing diagnostic path (for positioned input, `Position.markError`) and let the caller decide whether compilation continues. Reserve `enforce` for a checked boundary that cannot proceed.
- Add a focused `unittest` for each behavior change. Add or update a canonical grammar in `example/` when the behavior is observable in generated-compilation output.
- Write multi-line expected text as `` `...`.outdent.strip ``.
- Run the narrowest relevant test while iterating, then `dub test --config=example` for changes affecting the compiler pipeline.
- Update architecture documentation when a change invalidates a documented current boundary or invariant.

## Review conventions

Review against a concrete change request, not just the diff. For an interactive session, treat the user’s requests as the temporary specification and account for every request in a traceability list: request, evidence, and status. Resolve or explicitly surface every open item before handoff.

Review new code for the D conventions above, especially casts, range access, stable local bindings, domain names, mapping direction, and metadata boundaries. Report documented-standard breaches separately from design judgements.

For a change that crosses grammar construction, table generation, generated code, and runtime, review the complete path and its generated-output coverage. Do not accept a passing compile as evidence that the path’s semantics are preserved.

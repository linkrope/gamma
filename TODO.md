# Parked ideas

Possible future work, open questions, and side projects.
These are neither priorities nor implementation commitments.
When an idea becomes active, move its rationale and specification
to the relevant documentation, then remove it from this file.

## Migration and architecture

- **Continue merging epsilon into gamma.**
  Pick the next coherent Epsilon topic and assimilate it into Gamma.
- **Structure generated code.**
  Replace direct code fragments with an explicit representation,
  such as an abstract syntax tree or other intermediate language nodes.
- **Reconsider `.fix` templates for generated code.**
  Evaluate the `.fix` writer approach and record the decision, whether it is retained,
  replaced, or revised, in an ADR.
- **Use sum types where they clarify legacy state models.**
  Identify a concrete subtype hierarchy before pursuing this.

## Compiler behavior and diagnostics

- **Make generated-compiler tests safe to run in parallel.**
  Generated compilers currently share `libgamma_runtime.a` while building, so
  the suite runs single-threaded. Isolate that runtime artifact and restore
  parallel test execution.
- **Avoid speculative lexical syntax-tree construction.**
  The direct LR path still creates shared syntax-tree records while testing
  lexical candidates. The 0.398 MiB Oberon-0 probe retained 1,346,839
  records, allocated 6.41 GiB, and spent 1.58 s collecting. Profile and
  redesign that candidate path so only the chosen lexical match contributes
  records; do not begin table-lookup micro-optimizations first.
- **Eliminate empty LR lexer tables.**
  A tokenless grammar currently produces an unproductive synthetic lexer
  grammar and an empty lexer-table module only to satisfy the generated
  compiler's uniform imports. Stop before lexer-table generation and emit the
  direct end-of-input lexer instead.
- **Escape sequences.**
  Give equivalent escape spellings one terminal-symbol identity
  in generated compilers rather than copying their source spellings.
- **Predicate positions.**
  Decide where a failing predicate should be reported,
  including predicates after deeply nested terminals
  and analysis predicates on a left-hand side.
- **Generated-compiler output modes.**
  Investigate the current behavior, then separate detailed parser diagnostics
  from developer trace output.
- **Expressive, shared diagnostics.**
  Introduce one diagnostic reporter that owns reporting and error counting,
  and make generated-compiler diagnostics more useful.
- **Colorized Gamma output.**
  Use terminal color where it improves Gamma's diagnostics or other user-facing output.

## Language and compiler experiments

- **EAG-specified EBNF lowering.**
  Write an EAG-to-EAG compiler that lowers EBNF EAGs to BNF EAGs, including abbreviations.
  This is primarily a showcase for EAGs rather than production work.
- **Unicode lexer generation.**
  Replace the generated lexer's UTF-8 decision-tree workaround
  and consider a reserved `alpha` nonterminal for a Unicode letter.
- **Lexer declarations.**
  Explore declarative whitespace and comment rules:

  ```
  WhiteSpaces:
      "WHITESPACES" "ARE" char { "," char } ";" .

  Comments:
      Comment { ";" Comment } ";" .
  Comment:
      "COMMENTS" "FROM" char [ char ] "TO" char [ char ] ["NESTED"] .
  ```

- **RISC interpreter revival.**
  Extract and revive the ideal-RISC interpreter used by the Oberon-0 EAG
  in a separate project like this
  [the Asm directory](https://github.com/linkrope/programming-languages-and-compilers/tree/main/Asm).

## Cleanup experiments

- **Replace `Expand` helpers with `~`.**
  Array concatenation makes the affected implementations clearer and more idiomatic.

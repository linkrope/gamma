## Merger of epsilon and gamma

The gamma input parser and analyzer now parse and validate EAG specifications,
including affix forms. `gamma.input.EAGBuilder` converts the resulting model
to epsilon's EAG model for the existing LL(1)-based compiler generators.
The epsilon analyzer has been removed.

- Continue merging the remaining epsilon generator stages with gamma.

## Escape Sequences

- epsilon blindly copies escape sequences to the generated compiler
- but this makes `"\""` and `'"'` two different terminal symbols
- take, for example, the code from the gamma Scanner

## compiled compiler

- swap options `--info` and `--verbose`
  - `--info` should give detailed parser error messages
  - `--verbose` should print debug output

## epsilang.eag

- specify the lowering for EBNF and various abbreviations as an EAG

## Expand

- use ~ instead of Expand

## Code Generation

- create abstract syntax tree instead of writing code fragments

## Code Generation

- create intermediate language nodes

## UTF-8

- rewrite decision-tree implementation in generated lexer
  (current one is a workaround for the change to UTF-8 support)
- add reserved nonterminal "alpha" for Unicode letter?

## RISC Assembler

- revive RISC assembler?

## Lexer Generation

```
WhiteSpaces:
    "WHITESPACES" "ARE" char { "," char } ";" .

Comments:
    Comment { ";" Comment } ";" .
Comment:
    "COMMENTS" "FROM" char [ char ] "TO" char [ char ] ["NESTED"] .
```

## Replace Subtyping with Sum Type

- https://github.com/pbackus/sumtype

## Expressive Diagnostics

- https://clang.llvm.org/diagnostics.html

## Color

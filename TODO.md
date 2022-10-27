## Merger of epsilon and gamma

- epsilon is a full generator based on an LL(1) parser
- gamma is just an LALR(1) parser generator
- both need a lexer and parser for EAG specifications
- by now, we already changed gamma to use epsilon' s lexer
- since gamma uses a modern grammar model, we try the following approach:
  - we analyze grammar properties only with `gamma.input`
  - we finish `gamma.input`
  (handling of affix forms)
  - we transform the gamma grammar model into the epsilon grammar model
  (to reuse the compiler generation)
  - we remove the epsilon analyzer and move the lexer to `gamma.input.epsilang`

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

## Table Files

- include .Tab and .EvalTab files in executable

## Code Generation

- create intermediate language nodes

## History Set

- remove history state, tailored for Oberon's command execution

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

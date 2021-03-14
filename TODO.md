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

## String Representation

- add toString functions to simplify debugging

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

- revive RISC assembler

## Lexer Generation

```
WhiteSpaces:
    "WHITESPACES" "ARE" char { "," char } ";" .

Comments:
    Comment { ";" Comment } ";" .
Comment:
    "COMMENTS" "FROM" char [ char ] "TO" char [ char ] ["NESTED"] .
```

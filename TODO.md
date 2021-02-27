## compiled compiler

- swap options `--info` and `--verbose`
  - `--info` should give detailed parser error messages
  - `--verbose` should print debug output

## epsilon.eag

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

- no indent (use dfmt)
- create intermediate language nodes

## History Set

- remove history state, tailored for Oberon's command execution

## UTF-8

- rewrite decision-tree implementation in generated lexer
  (current one is a workaround for the change to UTF-8 support)
- add reserved nonterminal "alpha" for Unicode letter?

## RISC Assembler

- revive RISC assembler

## BitArray

- use `foreach (N; EAG.All)` instead of

```d
for (N = EAG.firstHNont; N < EAG.NextHNont; ++N)
    if (EAG.All[N])
```

## eIO.d

- get rid of (as much as possible of) eIO.d

## Output Directory

- introduce an output directory to be able to run tests in parallel

## epsilon.eag

- specify the lowering for EBNF and various abbreviations as an EAG

## Expand

- use ~ instead of Expand

## Forward Declarations

- remove code generation of commented out forward declarations

## Code Generation

- create abstract syntax tree instead of writing code fragments

## Range-based Scanner

- reintroduce range-based scanner from previous attempt

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

- generated scanner should support UTF-8

# Gamma

Gamma is a compiler generator whose input language combines meta grammars with
hyper grammars.

## Language

**Lexical nonterminal**:
A nonterminal that recognizes one lexical token in source input.
_Avoid_: Starred nonterminal

**Terminal**:
A literal token written in the grammar and matched directly in source input.
_Avoid_: Quoted terminal

**Compact syntax tree**:
The evaluator-compatible, contiguous representation of a parsed program's rule applications, constructed directly by lexing and parsing. It omits terminal occurrences.
_Avoid_: Epsilon syntax tree

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

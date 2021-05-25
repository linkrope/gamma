# Extended Affix Grammar Compiler Compiler

[![D](https://github.com/linkrope/gamma/actions/workflows/d.yml/badge.svg)](https://github.com/linkrope/gamma/actions/workflows/d.yml)

_gamma_ is a compiler compiler for the [Extended Affix Grammar] formalism.

## Usage

Use [dub] to run, build, or test the compiler compiler. For example:

    dub run -- example/abc.eag

Then, run the compiled compiler. For example:

    ./S test/abc

## Experimental

Use [dub] to run the experimental LALR(1) parser generator. For example:

    dub run :experimental -- example/gamma-test.eag -v

## Bibliography

[_Echte Compilergenerierung:\
Effiziente Implementierung einer abgeschlossenen Theorie_][1]

[_True Compiler Generation_][1a]\
[automatic translation of the German publication from 1997]

[_Ein Evaluatorgenerator für zwei heuristische Teilklassen\
Sequentiell Orientierbarer Erweiterter Affixgrammatiken_][2]

[_An Evaluator Generator for Two Heuristic Subclasses of\
Sequentially Orientable Extended Affix Grammars_][2a]\
[automatic translation of the German diploma thesis from 1998]

[1]: ../assets/doc/epsilon-red-series.german.pdf
[1a]: ../assets/doc/epsilon-red-series.adoc
[2]: ../assets/doc/soag/soag-diploma-thesis.german.pdf
[2a]: ../assets/doc/soag/soag-diploma-thesis.adoc

[dub]: http://code.dlang.org/
[extended affix grammar]: https://en.wikipedia.org/wiki/Extended_affix_grammar

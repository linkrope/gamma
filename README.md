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

[dub]: http://code.dlang.org/
[extended affix grammar]: https://en.wikipedia.org/wiki/Extended_affix_grammar
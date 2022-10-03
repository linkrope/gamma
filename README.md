<img src="../assets/doc/images/Greek_lc_gamma.svg" alt="gamma" width="100"/>

# Extended Affix Grammar Compiler Generator

[![D](https://github.com/linkrope/gamma/actions/workflows/d.yml/badge.svg)](https://github.com/linkrope/gamma/actions/workflows/d.yml)

_gamma_ is a compiler generator for the [Extended Affix Grammar] formalism.

See the [Wiki](https://github.com/linkrope/gamma/wiki) for detailed introductions, tutorials,
information on Extended Affix Grammars and compiler generators, and more.

## Usage

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/linkrope/gamma)

Run _gamma_ to generate a compiler for some of the available [examples](example).
For example:

    ./gamma example/abc.eag

Then, run the generated compiler. For example:

    ./S test/abc

Alternatively, use [dub] to run, build, or test the compiler generator.
For example:

    dub run -- example/abc.eag

## Experimental

Use [dub] to try out the experimental LALR(1) parser generator.
For example:

    dub run :experimental -- example/bnf/ab.eag -v

[dub]: http://code.dlang.org/
[extended affix grammar]: https://en.wikipedia.org/wiki/Extended_affix_grammar

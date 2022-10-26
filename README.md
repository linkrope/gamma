<img src="../assets/doc/images/Greek_lc_gamma.svg" alt="gamma" width="100"/>

# Extended Affix Grammar Compiler Generator

[![D](https://github.com/linkrope/gamma/actions/workflows/d.yml/badge.svg)](https://github.com/linkrope/gamma/actions/workflows/d.yml)
[![License](https://img.shields.io/badge/license-BSL_1.0-blue.svg)](https://raw.githubusercontent.com/linkrope/gamma/master/LICENSE_1_0.txt)
[![Dub Version](https://img.shields.io/dub/v/gamma.svg)](https://code.dlang.org/packages/gamma)

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

[dub]: http://code.dlang.org/
[extended affix grammar]: https://en.wikipedia.org/wiki/Extended_affix_grammar

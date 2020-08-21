# Extended Affix Grammar Compiler Compiler

![D](https://github.com/linkrope/epsilon/workflows/D/badge.svg)

_epsilon_ is a compiler compiler for the [Extended Affix Grammar] formalism.

## Usage

Use [dub] to run, build, or test the compiler compiler. For example:

    dub run -- example/abc.eag

Then, run the compiled compiler. For example:

    ./S test/abc

[dub]: http://code.dlang.org/
[extended affix grammar]: https://en.wikipedia.org/wiki/Extended_affix_grammar

<img src="../assets/doc/images/Greek_lc_gamma.svg" alt="gamma" width="100"/>

# Gamma: Extended Affix Grammar Compiler Generator

[![D](https://github.com/linkrope/gamma/actions/workflows/ci.yml/badge.svg)](https://github.com/linkrope/gamma/actions/workflows/ci.yml)
[![License](https://img.shields.io/badge/license-BSL_1.0-blue.svg)](https://raw.githubusercontent.com/linkrope/gamma/master/LICENSE_1_0.txt)
[![DUB version](https://img.shields.io/dub/v/gamma.svg)](https://code.dlang.org/packages/gamma)
<br/>
[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/linkrope/gamma)

_Gamma_ is a compiler generator for the [Extended Affix Grammar] (EAG) formalism.

Never heard of Extended Affix Grammars? They extend context-free grammars with affixes.
Extended Affix Grammars take a pure formal-languages approach:
they define syntax, semantic analysis, and code generation just with grammars.

Unlike [Attribute Grammars], the affix values are defined by another context-free grammar.
This is why Extended Affix Grammars are also called *two-level grammars*.

## Learn about Extended Affix Grammars

The [Wiki](https://github.com/linkrope/gamma/wiki) covers:

- [Introduction to Gamma](https://github.com/linkrope/gamma/wiki/Introduction-to-Gamma)
- [Introduction to Extended Affix Grammars](https://github.com/linkrope/gamma/wiki/Introduction-to-Extended-Affix-Grammars)
- [How to Specify Compilation Results](https://github.com/linkrope/gamma/wiki/How-to-Specify-Compilation-Results)
- [Table Lookup and Semantic Validation](https://github.com/linkrope/gamma/wiki/Table-Lookup-and-Semantic-Validation)
- [Writing Concise Grammar Specifications](https://github.com/linkrope/gamma/wiki/Writing-concise-grammar-specifications),<br/>
  especially by using EBNF, with the lowering described here
- [Affix Evaluation Procedures](https://github.com/linkrope/gamma/wiki/Affix-Evaluation-Procedures)

## Try Gamma

Open this repository in GitHub Codespaces using the badge above.

The compact [`example/decl-appl.eag`][declaration/application example] grammar tracks
declarations and applications, something a context-free grammar alone cannot express. Generate
its compiler with:

```sh
dub run -- example/decl-appl.eag
```

Gamma writes the generated `DeclAppl` compiler to the current directory. Run it on an application
of an undeclared identifier:

```sh
echo 'DECL ab APPL ba' | ./DeclAppl
```

The compiler reports that `ba` has not been declared.

For further experimentation, build the compiler generator as the `gamma` executable:

```sh
dub build
```

Use `gamma` to generate the full `OberonO` compiler (letter `O`, not digit `0`):

```sh
./gamma --space example/oberon0.eag
```

Run the generated `OberonO` compiler on some Oberon-0 source file:

```sh
./OberonO test/oberon0/Sample.Mod
```

## Status

Gamma is a work in progress. Eta, written in Pascal, was reimagined as Epsilon in Oberon and
restarted as Gamma in Java. Most of the Epsilon code has now been automatically converted to D
and is being assimilated into Gamma's new code.

## More

- Browse the [examples] for runnable grammars.
- Run `./gamma --help` to see compiler-generation options.
- To run Gamma locally, install the [D toolchain].

[extended affix grammar]: https://en.wikipedia.org/wiki/Extended_affix_grammar
[attribute grammars]: https://en.wikipedia.org/wiki/Attribute_grammar
[declaration/application example]: example/decl-appl.eag
[examples]: example
[d toolchain]: https://dlang.org/download.html

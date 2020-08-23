# SOAG

## example: abc

    dub run -- example/abc.eag --soag
    echo a a a b b b c c c | ./S

## example: ab

    dub run -- example/ab.eag --soag
    echo a a a b b b | ./S

    dub run -- example/ab-ebnf.eag --soag
    echo a a a b b b | ./S

## example: w w

    dub run -- example/w-w.eag --soag
    echo a b a b c a b a b | ./S

- [ ] FIXME: 0?
- [x] works when non-terminal is not merged with anonymous non-terminal

## example: hello world

    dub run -- example/hello-world.eag --soag

 - [x] FIXME: Conversion negative overflow

## example: count

    dub run -- example/count1.eag --soag
    echo i i i i i i i i i i i i i | ./S

    dub run -- example/count2.eag --soag
    echo a a a a a a a a a a a a a | ./S

    dub run -- example/count3.eag --soag
    echo | ./S

    dub run -- example/count5.eag --soag
    echo a a a b b b | ./S

    dub run -- example/count4.eag --soag
    echo a a a | ./S

- [ ] FIXME: 0?
- [x] works when non-terminal is not merged with anonymous non-terminal

## example: decl appl

    dub run -- example/decl-appl.eag --soag
    echo DECL a DECL b APPL a APPL b | ./DeclAppl

## example : ident list

    dub run -- example/ident-list.eag --soag
    echo abba | ./S

 - [ ] TODO: fix example

## example: optimize

    dub run -- example/example.eag --soag

- [ ] TODO: left recursion over non-terminals

## example: single sweep

    dub run -- example/single-sweep.eag --soag
    echo a b c d e | ./S

- [ ] FIXME: eSOAGOptimizer.d(118): Range violation
- [x] works without optimization

## example: not OEAG

    dub run -- example/not-oeag1.eag --soag
    echo b c | ./S

    dub run -- example/not-oeag2.eag --soag
    echo b c c | ./S

    dub run -- example/not-oeag3.eag --soag
    echo b a a | ./S

    dub run -- example/not-oeag4.eag --soag
    echo b a a | ./S

## example: eta

    dub run -- example/eta.eag --soag
    dub run -- example/eta-utf8.eag --soag
    ./Eta test/cola/PL0.Cola

- [ ] FIXME: EtaEval.d(5195): Range violation
- [x] works without optimization

## example: oberon 0

    dub run -- example/frontend.eag --soag
    dub run -- example/oberon0.eag --soag
    dub run -- example/unequal.eag --soag
    ./OberonO test/oberon0/Sample.Mod

    dub run -- example/abstract-syntax.eag --soag
    ./OberonOa test/oberon0/Sample.Mod

    dub run -- example/type-tables.eag --soag
    dub run -- example/type-resolution.eag --soag
    dub run -- example/symbol-tables.eag --soag
    dub run -- example/symbol-resolution.eag --soag
    dub run -- example/type-check.eag --soag

- [ ] FIXME: OberonOEval.d(394): Range violation
- [ ] FIXME: infinite loop
- [ ] FIXME: segmentation fault without optimization

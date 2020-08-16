dub run -- example/abc.eag --soag
echo a a a b b b c c c | ./S

dub run -- example/ab.eag --soag
echo a a a b b b | ./S

dub run -- example/ab-ebnf.eag --soag
echo a a a b b b | ./S

dub run -- example/w-w.eag --soag
echo a b a b c a b a b | ./S
FIXME: 0?

dub run -- example/hello-world.eag --soag
FIXME: Conversion negative overflow

dub run -- example/count1.eag --soag
echo i i i i i i i i i i i i i | ./S

dub run -- example/count2.eag --soag
echo a a a a a a a a a a a a a | ./S

dub run -- example/count3.eag --soag
echo | ./S

dub run -- example/count4.eag --soag
echo a a a | ./S
FIXME: 0?

dub run -- example/count5.eag --soag
echo a a a b b b | ./S

dub run -- example/decl-appl.eag --soag
echo DECL a DECL b APPL a APPL b | ./DeclAppl

dub run -- example/ident-list.eag --soag
echo abba | ./S
TODO: fix example

dub run -- example/example.eag --soag
TODO: left recursion over nonterminals

dub run -- example/single-sweep.eag --soag
FIXME: eSOAGOptimizer.d(118): Range violation

    dub run -- example/single-sweep.eag --soag -o
    echo a b c d e | ./S

dub run -- example/not-oeag1.eag --soag
TODO: left recursion over nonterminals

dub run -- example/not-oeag2.eag --soag
TODO: left recursion over nonterminals

dub run -- example/not-oeag3.eag --soag
TODO: left recursion over nonterminals

dub run -- example/not-oeag4.eag --soag
TODO: left recursion over nonterminals

dub run -- example/eta.eag --soag
dub run -- example/eta-utf8.eag --soag
./Eta test/cola/PL0.Cola
FIXME: EtaEval.d(5195): Range violation

dub run -- example/frontend.eag --soag
dub run -- example/oberon0.eag --soag
dub run -- example/unequal.eag --soag
./OberonO test/oberon0/Sample.Mod
FIXME: OberonOEval.d(394): Range violation

dub run -- example/abstract-syntax.eag --soag
./OberonOa test/oberon0/Sample.Mod
FIXME: infinite loop

    dub run -- example/type-tables.eag --soag
    dub run -- example/type-resolution.eag --soag
    dub run -- example/symbol-tables.eag --soag
    dub run -- example/symbol-resolution.eag --soag
    dub run -- example/type-check.eag --soag

module test.oberon0;

import std.format;
import test.helper;

@("compile and run Oberon-0 frontend")
unittest
{
    run("./epsilon example/frontend.eag")
        .shouldMatch("SLEAG testing   OberonO   ok");
    run("./OberonO test/oberon0/Sample.Mod")
        .shouldMatch("^done$");
    run("./OberonO test/oberon0/BigSample.Mod")
        .shouldMatch("^done$");
    run("./OberonO test/oberon0/Error.Mod")
        .shouldMatch("^  31 errors detected$");
}

static foreach (eag; ["oberon0.eag", "unequal.eag"])
    @(format!"compile %s and run Oberon-0 compiler"(eag))
    unittest
    {
        run("./epsilon --space example/" ~ eag)
            .shouldMatch("SLEAG testing   OberonO   ok");
        run("./OberonO test/oberon0/Sample.Mod")
            .shouldMatch("^L1 .* RET 0 $");
        run("./OberonO test/oberon0/BigSample.Mod")
            .shouldMatch("^^L1 .* RET 0 $$");
        run("./OberonO test/oberon0/Error.Mod")
            .shouldMatch("^  31 errors detected$");
    }

@("compile and run Oberon-0 compiler pipeline")
unittest
{
    run("./epsilon --space example/abstract-syntax.eag")
        .shouldMatch("SSweep testing OberonOa   ok");
    run("./epsilon --space example/type-tables.eag")
        .shouldMatch("SLEAG testing   OberonOb   ok");
    run("./epsilon --space example/type-resolution.eag")
        .shouldMatch("SSweep testing OberonOc   ok");
    run("./epsilon --space example/symbol-tables.eag")
        .shouldMatch("SLEAG testing   OberonOd   ok");
    run("./epsilon --space example/symbol-resolution.eag")
        .shouldMatch("SLEAG testing   OberonOe   ok");
    run("./epsilon --space example/type-check.eag")
        .shouldMatch("SSweep testing OberonOf   ok");

    run("./OberonOa -w test/oberon0/Sample.Mod")
        .shouldMatch("OberonOa compiler: compiling...");
    run("./OberonOb -w OberonOa.Out")
        .shouldMatch("OberonOb compiler: compiling...");
    run("./OberonOc -w OberonOb.Out")
        .shouldMatch("OberonOc compiler: compiling...");
    run("./OberonOd -w OberonOc.Out")
        .shouldMatch("OberonOd compiler: compiling...");
    run("./OberonOe -w OberonOd.Out")
        .shouldMatch("OberonOe compiler: compiling...");
    run("./OberonOf -w OberonOe.Out")
        .shouldMatch("OberonOf compiler: compiling...");
    run("cat OberonOf.Out")
        .shouldMatch("ID M u l t i p l y PROC");
}

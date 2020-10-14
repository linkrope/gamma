module test.oberon0;

import std.format;
import std.path;
import test.helper;

@("compile and run Oberon-0 frontend")
unittest
{
    with (sandbox)
    {
        run!"./epsilon example/frontend.eag --output-directory %s"(directory)
            .shouldMatch("SLEAG testing   OberonO   ok");
        run!"cd %s && ./OberonO %s"(directory, absolutePath("test/oberon0/Sample.Mod"))
            .shouldMatch("^done$");
        run!"cd %s && ./OberonO %s"(directory, absolutePath("test/oberon0/BigSample.Mod"))
            .shouldMatch("^done$");
        run!"cd %s && ./OberonO %s"(directory, absolutePath("test/oberon0/Error.Mod"))
            .shouldMatch("^  31 errors detected$");
    }
}

static foreach (eag; ["oberon0.eag", "unequal.eag"])
    @(format!"compile %s and run Oberon-0 compiler"(eag))
    unittest
    {
        with (sandbox)
        {
            run!"./epsilon --space example/%s --output-directory %s"(eag, directory)
                .shouldMatch("SLEAG testing   OberonO   ok");
            run!"cd %s && ./OberonO %s"(directory, absolutePath("test/oberon0/Sample.Mod"))
                .shouldMatch("^L1 .* RET 0 $");
            run!"cd %s && ./OberonO %s"(directory, absolutePath("test/oberon0/BigSample.Mod"))
                .shouldMatch("^^L1 .* RET 0 $$");
            run!"cd %s && ./OberonO %s"(directory, absolutePath("test/oberon0/Error.Mod"))
                .shouldMatch("^  31 errors detected$");
        }
    }

@("compile and run Oberon-0 compiler pipeline")
unittest
{
    with (sandbox)
    {
        run!"./epsilon --space example/abstract-syntax.eag --output-directory %s"(directory)
            .shouldMatch("SSweep testing OberonOa   ok");
        run!"./epsilon --space example/type-tables.eag --output-directory %s"(directory)
            .shouldMatch("SLEAG testing   OberonOb   ok");
        run!"./epsilon --space example/type-resolution.eag --output-directory %s"(directory)
            .shouldMatch("SSweep testing OberonOc   ok");
        run!"./epsilon --space example/symbol-tables.eag --output-directory %s"(directory)
            .shouldMatch("SLEAG testing   OberonOd   ok");
        run!"./epsilon --space example/symbol-resolution.eag --output-directory %s"(directory)
            .shouldMatch("SLEAG testing   OberonOe   ok");
        run!"./epsilon --space example/type-check.eag --output-directory %s"(directory)
            .shouldMatch("SSweep testing OberonOf   ok");

        run!"cd %s && ./OberonOa -w %s"(directory, absolutePath("test/oberon0/Sample.Mod"))
            .shouldMatch("OberonOa compiler: compiling...");
        run!"cd %s && ./OberonOb -w OberonOa.Out"(directory)
            .shouldMatch("OberonOb compiler: compiling...");
        run!"cd %s && ./OberonOc -w OberonOb.Out"(directory)
            .shouldMatch("OberonOc compiler: compiling...");
        run!"cd %s && ./OberonOd -w OberonOc.Out"(directory)
            .shouldMatch("OberonOd compiler: compiling...");
        run!"cd %s && ./OberonOe -w OberonOd.Out"(directory)
            .shouldMatch("OberonOe compiler: compiling...");
        run!"cd %s && ./OberonOf -w OberonOe.Out"(directory)
            .shouldMatch("OberonOf compiler: compiling...");
        run!"cd %s && cat OberonOf.Out"(directory)
            .shouldMatch("ID M u l t i p l y PROC");
    }
}

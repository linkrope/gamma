module test.oberon0;

import std.format;
import std.path;
import test.helper;

@("compile and run Oberon-0 frontend")
unittest
{
    with (sandbox)
    {
        run!"./gamma example/frontend.eag --output-directory %s"(directory)
            .shouldMatch("OberonO grammar is SLAG");
        run!"cd %s && ./OberonO %s"(directory, absolutePath("test/oberon0/Sample.Mod"))
            .shouldMatch("^done$");
        run!"cd %s && ./OberonO %s"(directory, absolutePath("test/oberon0/BigSample.Mod"))
            .shouldMatch("^done$");
        run!"cd %s && ./OberonO %s"(directory, absolutePath("test/oberon0/Error.Mod"))
            .shouldFail("^info: errors detected: 31$");
    }
}

static foreach (eag; ["oberon0.eag", "unequal.eag"])
    @(format!"compile %s and run Oberon-0 compiler"(eag))
    unittest
    {
        with (sandbox)
        {
            run!"./gamma --space example/%s --output-directory %s"(eag, directory)
                .shouldMatch("OberonO grammar is SLAG");
            run!"cd %s && ./OberonO %s"(directory, absolutePath("test/oberon0/Sample.Mod"))
                .shouldMatch("^L1 .* RET 0 $");
            run!"cd %s && ./OberonO %s"(directory, absolutePath("test/oberon0/BigSample.Mod"))
                .shouldMatch("^^L1 .* RET 0 $$");
            run!"cd %s && ./OberonO %s"(directory, absolutePath("test/oberon0/Error.Mod"))
                .shouldFail("^info: errors detected: 31$");
        }
    }

@("compile and run Oberon-0 compiler pipeline")
unittest
{
    with (sandbox)
    {
        run!"./gamma --space example/abstract-syntax.eag --output-directory %s"(directory)
            .shouldMatch("OberonOa grammar is single sweep");
        run!"./gamma --space example/type-tables.eag --output-directory %s"(directory)
            .shouldMatch("OberonOb grammar is SLAG");
        run!"./gamma --space example/type-resolution.eag --output-directory %s"(directory)
            .shouldMatch("OberonOc grammar is single sweep");
        run!"./gamma --space example/symbol-tables.eag --output-directory %s"(directory)
            .shouldMatch("OberonOd grammar is SLAG");
        run!"./gamma --space example/symbol-resolution.eag --output-directory %s"(directory)
            .shouldMatch("OberonOe grammar is SLAG");
        run!"./gamma --space example/type-check.eag --output-directory %s"(directory)
            .shouldMatch("OberonOf grammar is single sweep");

        run!"cd %s && ./OberonOa -v -w %s"(directory, absolutePath("test/oberon0/Sample.Mod"))
            .shouldMatch("OberonOa compiler: compiling...");
        run!"cd %s && ./OberonOb -v -w OberonOa.Out"(directory)
            .shouldMatch("OberonOb compiler: compiling...");
        run!"cd %s && ./OberonOc -v -w OberonOb.Out"(directory)
            .shouldMatch("OberonOc compiler: compiling...");
        run!"cd %s && ./OberonOd -v -w OberonOc.Out"(directory)
            .shouldMatch("OberonOd compiler: compiling...");
        run!"cd %s && ./OberonOe -v -w OberonOd.Out"(directory)
            .shouldMatch("OberonOe compiler: compiling...");
        run!"cd %s && ./OberonOf -v -w OberonOe.Out"(directory)
            .shouldMatch("OberonOf compiler: compiling...");
        run!"cd %s && cat OberonOf.Out"(directory)
            .shouldMatch("ID M u l t i p l y PROC");
    }
}

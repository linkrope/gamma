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
            .shouldPassWith("OberonO grammar is SLAG");
        run!"cd %s && ./OberonO -t %s"(directory, absolutePath("test/oberon0/Sample.Mod"))
            .shouldPassWith("^done$");
        run!"cd %s && ./OberonO -t %s"(directory, absolutePath("test/oberon0/BigSample.Mod"))
            .shouldPassWith("^done$");
        run!"cd %s && ./OberonO -t %s"(directory, absolutePath("test/oberon0/Error.Mod"))
            .shouldFailWith("^info: errors detected: 31$");
    }
}

static foreach (eag; ["oberon0.eag", "unequal.eag"])
    @(format!"compile %s and run Oberon-0 compiler"(eag))
    unittest
    {
        with (sandbox)
        {
            run!"./gamma --space example/%s --output-directory %s"(eag, directory)
                .shouldPassWith("OberonO grammar is SLAG");
            run!"cd %s && ./OberonO -t %s"(directory, absolutePath("test/oberon0/Sample.Mod"))
                .shouldPassWith("^L1 .* RET 0 $");
            run!"cd %s && ./OberonO -t %s"(directory, absolutePath("test/oberon0/BigSample.Mod"))
                .shouldPassWith("^^L1 .* RET 0 $$");
            run!"cd %s && ./OberonO -t %s"(directory, absolutePath("test/oberon0/Error.Mod"))
                .shouldFailWith("^info: errors detected: 31$");
        }
    }

@("compile and run Oberon-0 compiler pipeline")
unittest
{
    with (sandbox)
    {
        run!"./gamma --space example/abstract-syntax.eag --output-directory %s"(directory)
            .shouldPassWith("OberonOa grammar is single sweep");
        run!"./gamma --space example/type-tables.eag --output-directory %s"(directory)
            .shouldPassWith("OberonOb grammar is SLAG");
        run!"./gamma --space example/type-resolution.eag --output-directory %s"(directory)
            .shouldPassWith("OberonOc grammar is single sweep");
        run!"./gamma --space example/symbol-tables.eag --output-directory %s"(directory)
            .shouldPassWith("OberonOd grammar is SLAG");
        run!"./gamma --space example/symbol-resolution.eag --output-directory %s"(directory)
            .shouldPassWith("OberonOe grammar is SLAG");
        run!"./gamma --space example/type-check.eag --output-directory %s"(directory)
            .shouldPassWith("OberonOf grammar is single sweep");

        run!"cd %s && ./OberonOa -t -v -w %s"(directory, absolutePath("test/oberon0/Sample.Mod"))
            .shouldPassWith("OberonOa compiler: compiling...");
        run!"cd %s && ./OberonOb -t -v -w OberonOa.Out"(directory)
            .shouldPassWith("OberonOb compiler: compiling...");
        run!"cd %s && ./OberonOc -t -v -w OberonOb.Out"(directory)
            .shouldPassWith("OberonOc compiler: compiling...");
        run!"cd %s && ./OberonOd -t -v -w OberonOc.Out"(directory)
            .shouldPassWith("OberonOd compiler: compiling...");
        run!"cd %s && ./OberonOe -t -v -w OberonOd.Out"(directory)
            .shouldPassWith("OberonOe compiler: compiling...");
        run!"cd %s && ./OberonOf -t -v -w OberonOe.Out"(directory)
            .shouldPassWith("OberonOf compiler: compiling...");
        run!"cd %s && cat OberonOf.Out"(directory)
            .shouldPassWith("ID M u l t i p l y PROC");
    }
}

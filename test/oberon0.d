module test.oberon0;

import std.file;
import std.format;
import std.path;
import test.helper;

@("compile and run Oberon-0 frontend")
unittest
{
    with (sandbox)
    {
        run!"./gamma %s --output-directory %s"(buildPath("example", "frontend.eag"), directory)
            .shouldPassWith("OberonO grammar is SLAG");
        run!"cd %s && ./OberonO %s"(directory, absolutePath("test/oberon0/Sample.Mod"))
            .shouldPassWith("^done$");
        run!"cd %s && ./OberonO %s"(directory, absolutePath("test/oberon0/BigSample.Mod"))
            .shouldPassWith("^done$");
        run!"cd %s && ./OberonO %s"(directory, absolutePath("test/oberon0/Error.Mod"))
            .shouldFailWith("^info: errors detected: 31$");
    }
}

static foreach (eag; ["oberon0.eag", "unequal.eag"])
    @(format!"compile %s and run Oberon-0 compiler"(eag))
    unittest
    {
        with (sandbox)
        {
            run!"./gamma --space %s --output-directory %s"(buildPath("example", eag), directory)
                .shouldPassWith("OberonO grammar is SLAG");
            run!"cd %s && ./OberonO %s"(directory, absolutePath("test/oberon0/Sample.Mod"))
                .shouldPassWith("^L1 .* RET 0 $");
            run!"cd %s && ./OberonO %s"(directory, absolutePath("test/oberon0/BigSample.Mod"))
                .shouldPassWith("^^L1 .* RET 0 $$");
            run!"cd %s && ./OberonO %s"(directory, absolutePath("test/oberon0/Error.Mod"))
                .shouldFailWith("^info: errors detected: 31$");
        }
    }

@("compile and run Oberon-0 compiler pipeline")
unittest
{
    import std.regex : matchFirst, regex;

    with (sandbox)
    {
        run!"./gamma --space %s --output-directory %s"(buildPath("example", "abstract-syntax.eag"), directory)
            .shouldPassWith("OberonOa grammar is single sweep");
        run!"./gamma --space %s --output-directory %s"(buildPath("example", "type-tables.eag"), directory)
            .shouldPassWith("OberonOb grammar is SLAG");
        run!"./gamma --space %s --output-directory %s"(buildPath("example", "type-resolution.eag"), directory)
            .shouldPassWith("OberonOc grammar is single sweep");
        run!"./gamma --space %s --output-directory %s"(buildPath("example", "symbol-tables.eag"), directory)
            .shouldPassWith("OberonOd grammar is SLAG");
        run!"./gamma --space %s --output-directory %s"(buildPath("example", "symbol-resolution.eag"), directory)
            .shouldPassWith("OberonOe grammar is SLAG");
        run!"./gamma --space %s --output-directory %s"(buildPath("example", "type-check.eag"), directory)
            .shouldPassWith("OberonOf grammar is single sweep");

        run!"cd %s && ./OberonOa -v -w %s"(directory, absolutePath("test/oberon0/Sample.Mod"))
            .shouldPassWith("OberonOa compiler: compiling...");
        run!"cd %s && ./OberonOb -v -w OberonOa.Out"(directory)
            .shouldPassWith("OberonOb compiler: compiling...");
        run!"cd %s && ./OberonOc -v -w OberonOb.Out"(directory)
            .shouldPassWith("OberonOc compiler: compiling...");
        run!"cd %s && ./OberonOd -v -w OberonOc.Out"(directory)
            .shouldPassWith("OberonOd compiler: compiling...");
        run!"cd %s && ./OberonOe -v -w OberonOd.Out"(directory)
            .shouldPassWith("OberonOe compiler: compiling...");
        run!"cd %s && ./OberonOf -v -w OberonOe.Out"(directory)
            .shouldPassWith("OberonOf compiler: compiling...");

        const output = readText(buildPath(directory, "OberonOf.Out"));

        assert(output.matchFirst(regex("ID M u l t i p l y PROC", "m")), output);
    }
}

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
        run!"%s %s --output-directory %s"(gamma, buildPath("example", "frontend.eag"), directory)
            .shouldPassWith("OberonO grammar is SLAG");
        run!"cd %s && %s %s"(directory, dotSlash("OberonO"), absolutePath("test/oberon0/Sample.Mod"))
            .shouldPassWith("^done$");
        run!"cd %s && %s %s"(directory,  dotSlash("OberonO"), absolutePath("test/oberon0/BigSample.Mod"))
            .shouldPassWith("^done$");
        run!"cd %s && %s %s"(directory,  dotSlash("OberonO"), absolutePath("test/oberon0/Error.Mod"))
            .shouldFailWith("^info: errors detected: 31$");
    }
}

static foreach (eag; ["oberon0.eag", "unequal.eag"])
    @(format!"compile %s and run Oberon-0 compiler"(eag))
    unittest
    {
        with (sandbox)
        {
            run!"%s --space %s --output-directory %s"(gamma, buildPath("example", eag), directory)
                .shouldPassWith("OberonO grammar is SLAG");
            run!"cd %s && %s %s"(directory,  dotSlash("OberonO"), absolutePath("test/oberon0/Sample.Mod"))
                .shouldPassWith("^L1 .* RET 0 $");
            run!"cd %s && %s %s"(directory,  dotSlash("OberonO"), absolutePath("test/oberon0/BigSample.Mod"))
                .shouldPassWith("^^L1 .* RET 0 $$");
            run!"cd %s && %s %s"(directory,  dotSlash("OberonO"), absolutePath("test/oberon0/Error.Mod"))
                .shouldFailWith("^info: errors detected: 31$");
        }
    }

@("compile and run Oberon-0 compiler pipeline")
unittest
{
    with (sandbox)
    {
        run!"%s --space %s --output-directory %s"(gamma, buildPath("example", "abstract-syntax.eag"), directory)
            .shouldPassWith("OberonOa grammar is single sweep");
        run!"%s --space %s --output-directory %s"(gamma, buildPath("example", "type-tables.eag"), directory)
            .shouldPassWith("OberonOb grammar is SLAG");
        run!"%s --space %s --output-directory %s"(gamma, buildPath("example", "type-resolution.eag"), directory)
            .shouldPassWith("OberonOc grammar is single sweep");
        run!"%s --space %s --output-directory %s"(gamma, buildPath("example", "symbol-tables.eag"), directory)
            .shouldPassWith("OberonOd grammar is SLAG");
        run!"%s --space %s --output-directory %s"(gamma, buildPath("example", "symbol-resolution.eag"), directory)
            .shouldPassWith("OberonOe grammar is SLAG");
        run!"%s --space %s --output-directory %s"(gamma, buildPath("example", "type-check.eag"), directory)
            .shouldPassWith("OberonOf grammar is single sweep");

        run!"cd %s && %sa -v -w %s"(directory,  dotSlash("OberonO"), absolutePath("test/oberon0/Sample.Mod"))
            .shouldPassWith("OberonOa compiler: compiling...");
        run!"cd %s && %sb -v -w OberonOa.Out"(directory, dotSlash("OberonO"))
            .shouldPassWith("OberonOb compiler: compiling...");
        run!"cd %s && %sc -v -w OberonOb.Out"(directory, dotSlash("OberonO"))
            .shouldPassWith("OberonOc compiler: compiling...");
        run!"cd %s && %sd -v -w OberonOc.Out"(directory, dotSlash("OberonO"))
            .shouldPassWith("OberonOd compiler: compiling...");
        run!"cd %s && %se -v -w OberonOd.Out"(directory, dotSlash("OberonO"))
            .shouldPassWith("OberonOe compiler: compiling...");
        run!"cd %s && %sf -v -w OberonOe.Out"(directory, dotSlash("OberonO"))
            .shouldPassWith("OberonOf compiler: compiling...");

        const output = readText(buildPath(directory, "OberonOf.Out"));

        assert(output.matches("ID M u l t i p l y PROC"), output);
    }
}

module test.oberon0;

import std.file;
import std.format;
import std.path;
import test.helper;

// dfmt off
static foreach (parser; parsers)
    static foreach (evaluator; evaluators)
        static if (parser.name == "ELL" || evaluator.name != "SLAG")
        {
            @(format!"compile and run Oberon-0 frontend with %s and %s"(parser.name, evaluator.name))
            unittest
            {
                testFrontend(parser, evaluator);
            }

            static foreach (eag; ["oberon0.eag", "unequal.eag"])
                @(format!"compile %s with %s and %s and run Oberon-0 compiler"(eag, parser.name, evaluator.name))
                unittest
                {
                    testCompiler(eag, parser, evaluator);
                }

            static if (evaluator.name != "SLAG")
                @(format!"compile and run Oberon-0 compiler pipeline with %s and %s"(parser.name, evaluator.name))
                unittest
                {
                    testPipeline(parser, evaluator);
                }
        }
// dfmt on

void testFrontend(Parser parser, Evaluator evaluator)
{
    with (sandbox)
    {
        run!"%s %s %s --space %s --output-directory %s"(
            gamma, parser.arguments, evaluator.arguments, buildPath("example", "frontend.eag"), directory)
            .shouldPassWith(evaluator.successMessage);
        run!"cd %s && %s %s"(directory, dotSlash("OberonO"), absolutePath("test/oberon0/Sample.Mod"))
            .shouldPassWith("^ *done *$");
        run!"cd %s && %s %s"(directory, dotSlash("OberonO"), absolutePath("test/oberon0/BigSample.Mod"))
            .shouldPassWith("^ *done *$");
    }
}

void testCompiler(const string eag, Parser parser, Evaluator evaluator)
{
    with (sandbox)
    {
        run!"%s %s %s --space %s --output-directory %s"(
            gamma, parser.arguments, evaluator.arguments, buildPath("example", eag), directory)
            .shouldPassWith(evaluator.successMessage);
        run!"cd %s && %s %s"(directory, dotSlash("OberonO"), absolutePath("test/oberon0/Sample.Mod"))
            .shouldPassWith("^L1 .* RET 0 $");
        run!"cd %s && %s %s"(directory, dotSlash("OberonO"), absolutePath("test/oberon0/BigSample.Mod"))
            .shouldPassWith("^^L1 .* RET 0 $$");
        run!"cd %s && %s %s"(directory, dotSlash("OberonO"), absolutePath("test/oberon0/Error.Mod"))
            .shouldFailWith(parser.errorPattern);
    }
}

void testPipeline(Parser parser, Evaluator evaluator)
{
    with (sandbox)
    {
        foreach (eag; [
            "abstract-syntax.eag",
            "type-tables.eag",
            "type-resolution.eag",
            "symbol-tables.eag",
            "symbol-resolution.eag",
            "type-check.eag",
        ])
        {
            run!"%s %s %s --space %s --output-directory %s"(
                gamma, parser.arguments, evaluator.arguments, buildPath("example", eag), directory)
                .shouldPass;
        }

        run!"cd %s && %sa -w %s"(directory, dotSlash("OberonO"), absolutePath("test/oberon0/Sample.Mod"))
            .shouldPass;
        run!"cd %s && %sb -w OberonOa.Out"(directory, dotSlash("OberonO"))
            .shouldPass;
        run!"cd %s && %sc -w OberonOb.Out"(directory, dotSlash("OberonO"))
            .shouldPass;
        run!"cd %s && %sd -w OberonOc.Out"(directory, dotSlash("OberonO"))
            .shouldPass;
        run!"cd %s && %se -w OberonOd.Out"(directory, dotSlash("OberonO"))
            .shouldPass;
        run!"cd %s && %sf -w OberonOe.Out"(directory, dotSlash("OberonO"))
            .shouldPass;

        const output = readText(buildPath(directory, "OberonOf.Out"));

        assert(output.matches("ID M u l t i p l y PROC"), output);
    }
}

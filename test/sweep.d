module test.sweep;

import std.file;
import std.format;
import std.path;
import test.helper;

static foreach (parser; parsers)
{
    @(format!"compile abc.eag as Single-Sweep with %s and run compiler"(parser.name))
    unittest
    {
        with (sandbox)
        {
            run!"%s %s --sweep --space %s --output-directory %s"(
                gamma, parser.arguments, buildPath("example", "abc.eag"), directory)
                .shouldPassWith("S grammar is single sweep");
            run!"cd %s && echo a a a b b b c c c | %s"(directory, dotSlash("S"))
                .shouldPassWith(`^1 1 1 $`);
        }
    }

    @(format!"compile ab.eag as Single-Sweep with %s and run compiler"(parser.name))
    unittest
    {
        with (sandbox)
        {
            run!"%s %s --sweep --space %s --output-directory %s"(
                gamma, parser.arguments, buildPath("example", "ab.eag"), directory)
                .shouldPassWith("S grammar is single sweep");
            run!"cd %s && echo a a a b b b | %s"(directory, dotSlash("S"))
                .shouldPassWith("^1 1 1 $");
        }
    }

    @(format!"compile bnf/ab.eag as Single-Sweep with %s and run compiler"(parser.name))
    unittest
    {
        with (sandbox)
        {
            run!"%s %s --sweep --space %s --output-directory %s"(
                gamma, parser.arguments, buildPath("example", "bnf", "ab.eag"), directory)
                .shouldPassWith("S grammar is single sweep");
            run!"cd %s && echo a a a b b b | %s"(directory, dotSlash("S"))
                .shouldPassWith("^1 1 1 $");
        }
    }

    @(format!"compile w-w.eag as Single-Sweep with %s and run compiler"(parser.name))
    unittest
    {
        with (sandbox)
        {
            run!"%s %s --sweep --space %s --output-directory %s"(
                gamma, parser.arguments, buildPath("example", "w-w.eag"), directory)
                .shouldPassWith("S grammar is single sweep");
            run!"cd %s && echo a b a b c a b a b | %s"(directory, dotSlash("S"))
                .shouldPassWith("^a b a b $");
        }
    }

    @(format!"compile hello-world.eag as Single-Sweep with %s and run compiler"(parser.name))
    unittest
    {
        with (sandbox)
        {
            write(buildPath(directory, "input"), null);
            run!"%s %s --sweep %s --output-directory %s"(
                gamma, parser.arguments, buildPath("example", "hello-world.eag"), directory)
                .shouldPassWith("S grammar is single sweep");
            run!"cd %s && %s input"(directory, dotSlash("S"))
                .shouldPassWith("^Hello World!$");
        }
    }

    @(format!"compile count1.eag as Single-Sweep with %s and run compiler"(parser.name))
    unittest
    {
        with (sandbox)
        {
            run!"%s %s --sweep --space %s --output-directory %s"(
                gamma, parser.arguments, buildPath("example", "count1.eag"), directory)
                .shouldPassWith("S grammar is single sweep");
            run!"cd %s && echo 1 1 1 1 1 1 1 1 1 1 1 1 1 | %s"(directory, dotSlash("S"))
                .shouldPassWith("^Number 1 3 $");
        }
    }

    @(format!"compile count6.eag as Single-Sweep with %s and run compiler"(parser.name))
    unittest
    {
        with (sandbox)
        {
            run!"%s %s --sweep %s --output-directory %s"(
                gamma, parser.arguments, buildPath("example", "count6.eag"), directory)
                .shouldPassWith("S grammar is single sweep");
            run!"cd %s && echo a a a b b b | %s"(directory, dotSlash("S"))
                .shouldPassWith("^3$");
        }
    }

    @(format!"compile decl-appl.eag as Single-Sweep with %s and run compiler"(parser.name))
    unittest
    {
        with (sandbox)
        {
            run!"%s %s --sweep --space %s --output-directory %s"(
                gamma, parser.arguments, buildPath("example", "decl-appl.eag"), directory)
                .shouldPassWith("DeclAppl grammar is single sweep");
            run!"cd %s && echo DECL ab DECL ba APPL ab | %s"(directory, dotSlash("DeclAppl"))
                .shouldPassWith("^ba ; ab ; $");
        }
    }

    @(format!"single-sweep predicate position follows grammar order with %s"(parser.name))
    unittest
    {
        with (sandbox)
        {
            write(buildPath(directory, "input"), "a\nb\n");
            run!"%s %s --sweep --space %s --output-directory %s"(
                gamma, parser.arguments, buildPath("example", "predicate-order.eag"), directory)
                .shouldPassWith("PredicateOrder grammar is single sweep");
            run!"cd %s && %s input"(directory, dotSlash("PredicateOrder"))
                .shouldFailWith(`error: predicate 'Matches' failed\ninput:1:1 a`);
        }
    }

    @(format!"compile single-sweep.eag as Single-Sweep with %s and run compiler"(parser.name))
    unittest
    {
        with (sandbox)
        {
            run!"%s %s --sweep %s --output-directory %s"(
                gamma, parser.arguments, buildPath("example", "single-sweep.eag"), directory)
                .shouldPassWith("S grammar is single sweep");
            run!"cd %s && echo a b c d e | %s"(directory, dotSlash("S"))
                .shouldPassWith("^$");
        }
    }
}

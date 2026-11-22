module test.soag;

import core.exception;
import std.exception;
import std.file;
import std.format;
import std.path;
import test.helper;

static foreach (parser; parserExamples)
{
@ (format!"compile abc.eag as SOAG with %s parser and run compiler"(parser.name))
unittest
{
    with (sandbox)
    {
        run!"%s %s --soag --space %s --output-directory %s"(
            gamma, parser.arguments, buildPath("example", "abc.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo a a a b b b c c c | %s"(directory, dotSlash("S"))
            .shouldPassWith(`^1 1 1 $`);
    }
}

@ (format!"compile ab.eag as SOAG with %s parser and run compiler"(parser.name))
unittest
{
    with (sandbox)
    {
        run!"%s %s --soag --space %s --output-directory %s"(
            gamma, parser.arguments, buildPath("example", "ab.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo a a a b b b | %s"(directory, dotSlash("S"))
            .shouldPassWith("^1 1 1 $");
    }
}

@ (format!"compile bnf/ab.eag as SOAG with %s parser and run compiler"(parser.name))
unittest
{
    with (sandbox)
    {
        run!"%s %s --soag --space %s --output-directory %s"(
            gamma, parser.arguments, buildPath("example", "bnf", "ab.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo a a a b b b | %s"(directory, dotSlash("S"))
            .shouldPassWith("^1 1 1 $");
    }
}

@ (format!"compile w-w.eag as SOAG with %s parser and run compiler"(parser.name))
unittest
{
    with (sandbox)
    {
        run!"%s %s --soag --space %s --output-directory %s"(
            gamma, parser.arguments, buildPath("example", "w-w.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo a b a b c a b a b | %s"(directory, dotSlash("S"))
            .shouldPassWith("^a b a b $");
    }
}

@ (format!"compile w-w-soag.eag as SOAG with %s parser and run compiler"(parser.name))
unittest
{
    with (sandbox)
    {
        run!"%s %s --soag --space %s --output-directory %s"(
            gamma, parser.arguments, buildPath("example", "w-w-soag.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo a b a b c a b a b | %s"(directory, dotSlash("S"))
            .shouldPassWith("^a b a b $");
    }
}

@ (format!"compile hello-world.eag as SOAG with %s parser and run compiler"(parser.name))
unittest
{
    with (sandbox)
    {
        write(buildPath(directory, "input"), null);
        run!"%s %s --soag %s --output-directory %s"(
            gamma, parser.arguments, buildPath("example", "hello-world.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && %s input"(directory, dotSlash("S"))
            .shouldPassWith("^Hello World!$");
    }
}

@ (format!"compile count1.eag as SOAG with %s parser and run compiler"(parser.name))
unittest
{
    with (sandbox)
    {
        run!"%s %s --soag --space %s --output-directory %s"(
            gamma, parser.arguments, buildPath("example", "count1.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo 1 1 1 1 1 1 1 1 1 1 1 1 1 | %s"(directory, dotSlash("S"))
            .shouldPassWith("^Number 1 3 $");
    }
}

@ (format!"compile count2.eag as SOAG with %s parser and run compiler"(parser.name))
unittest
{
    with (sandbox)
    {
        run!"%s %s --soag %s --output-directory %s"(
            gamma, parser.arguments, buildPath("example", "count2.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo a a a a a a a a a a a a a | %s"(directory, dotSlash("S"))
            .shouldPassWith("^13$");
    }
}

@ (format!"compile count3.eag as SOAG with %s parser and run compiler"(parser.name))
unittest
{
    with (sandbox)
    {
        write(buildPath(directory, "input"), null);
        run!"%s %s --soag %s --output-directory %s"(
            gamma, parser.arguments, buildPath("example", "count3.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && %s input"(directory, dotSlash("S"))
            .shouldPassWith("^0$");
    }
}

@ (format!"compile count4.eag as SOAG with %s parser and run compiler"(parser.name))
unittest
{
    with (sandbox)
    {
        run!"%s %s --soag %s --output-directory %s"(
            gamma, parser.arguments, buildPath("example", "count4.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo a a a | %s"(directory, dotSlash("S"))
            .shouldPassWith("^3$");
    }
}

@ (format!"compile count5.eag as SOAG with %s parser and run compiler"(parser.name))
unittest
{
    with (sandbox)
    {
        run!"%s %s --soag %s --output-directory %s"(
            gamma, parser.arguments, buildPath("example", "count5.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo a a a | %s"(directory, dotSlash("S"))
            .shouldPassWith("^3$");
    }
}

@ (format!"compile count6.eag as SOAG with %s parser and run compiler"(parser.name))
unittest
{
    with (sandbox)
    {
        run!"%s %s --soag %s --output-directory %s"(
            gamma, parser.arguments, buildPath("example", "count6.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo a a a b b b | %s"(directory, dotSlash("S"))
            .shouldPassWith("^3$");
    }
}

@ (format!"compile decl-appl.eag as SOAG with %s parser and run compiler"(parser.name))
unittest
{
    with (sandbox)
    {
        run!"%s %s --soag --space %s --output-directory %s"(
            gamma, parser.arguments, buildPath("example", "decl-appl.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo DECL ab DECL ba APPL ab | %s"(directory, dotSlash("DeclAppl"))
            .shouldPassWith("^ba ; ab ; $");
    }
}

@ (format!"compile example.eag as SOAG with %s parser and run compiler"(parser.name))
unittest
{
    with (sandbox)
    {
        run!"%s %s --soag %s --output-directory %s"(
            gamma, parser.arguments, buildPath("example", "example.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo a b e 1 | %s"(directory, dotSlash("P"))
            .shouldPassWith("^1$");
    }
}

@ (format!"compile single-sweep.eag as SOAG with %s parser and run compiler"(parser.name))
unittest
{
    with (sandbox)
    {
        run!"%s %s --soag %s --output-directory %s"(
            gamma, parser.arguments, buildPath("example", "single-sweep.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo a b c d e | %s"(directory, dotSlash("S"))
            .shouldPassWith("^$");
    }
}

@ (format!"compile single-sweep.eag as SOAG without optimization with %s parser and run compiler"(
    parser.name))
unittest
{
    with (sandbox)
    {
        run!"%s %s --soag -o %s --output-directory %s"(
            gamma, parser.arguments, buildPath("example", "single-sweep.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo a b c d e | %s"(directory, dotSlash("S"))
            .shouldPassWith("^$");
    }
}

@ (format!"compile non-oag1.eag as SOAG with %s parser and run compiler"(parser.name))
unittest
{
    with (sandbox)
    {
        run!"%s %s --soag %s --output-directory %s"(
            gamma, parser.arguments, buildPath("example", "non-oag1.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo b c | %s"(directory, dotSlash("S"))
            .shouldPassWith("^0$");
    }
}

@ (format!"compile non-oag2.eag as SOAG with %s parser and run compiler"(parser.name))
unittest
{
    with (sandbox)
    {
        run!"%s %s --soag %s --output-directory %s"(
            gamma, parser.arguments, buildPath("example", "non-oag2.eag"), directory)
            .shouldPassWith(`grammar is SOAG \(backtracked\)`);
        run!"cd %s && echo b c c | %s"(directory, dotSlash("S"))
            .shouldPassWith("^0$");
    }
}

@ (format!"compile non-oag3.eag as SOAG with %s parser and run compiler"(parser.name))
unittest
{
    with (sandbox)
    {
        run!"%s %s --soag %s --output-directory %s"(
            gamma, parser.arguments, buildPath("example", "non-oag3.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo b a a | %s"(directory, dotSlash("S"))
            .shouldPassWith("^0$");
    }
}

@ (format!"compile non-oag4.eag as SOAG with %s parser and run compiler"(parser.name))
unittest
{
    with (sandbox)
    {
        run!"%s %s --soag %s --output-directory %s"(
            gamma, parser.arguments, buildPath("example", "non-oag4.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo b a a | %s"(directory, dotSlash("S"))
            .shouldPassWith("^0$");
    }
}
}

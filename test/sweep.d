module test.sweep;

import std.file;
import std.path;
import test.helper;

@("compile abc.eag as Single-Sweep and run compiler")
unittest
{
    with (sandbox)
    {
        run!"%s --sweep --space %s --output-directory %s"(gamma, buildPath("example", "abc.eag"), directory)
            .shouldPassWith("S grammar is single sweep");
        run!"cd %s && echo a a a b b b c c c | %s"(directory, dotSlash("S"))
            .shouldPassWith(`^1 1 1 $`);
    }
}

@("compile ab.eag as Single-Sweep and run compiler")
unittest
{
    with (sandbox)
    {
        run!"%s --sweep --space %s --output-directory %s"(gamma, buildPath("example", "ab.eag"), directory)
            .shouldPassWith("S grammar is single sweep");
        run!"cd %s && echo a a a b b b | %s"(directory, dotSlash("S"))
            .shouldPassWith("^1 1 1 $");
    }
}

@("compile bnf/ab.eag as Single-Sweep and run compiler")
unittest
{
    with (sandbox)
    {
        run!"%s --sweep --space %s --output-directory %s"(gamma, buildPath("example", "bnf", "ab.eag"), directory)
            .shouldPassWith("S grammar is single sweep");
        run!"cd %s && echo a a a b b b | %s"(directory, dotSlash("S"))
            .shouldPassWith("^1 1 1 $");
    }
}

@("compile w-w.eag as Single-Sweep and run compiler")
unittest
{
    with (sandbox)
    {
        run!"%s --sweep --space %s --output-directory %s"(gamma, buildPath("example", "w-w.eag"), directory)
            .shouldPassWith("S grammar is single sweep");
        run!"cd %s && echo a b a b c a b a b | %s"(directory, dotSlash("S"))
            .shouldPassWith("^a b a b $");
    }
}

@("compile hello-world.eag as Single-Sweep and run compiler")
unittest
{
    with (sandbox)
    {
        write(buildPath(directory, "input"), null);
        run!"%s --sweep %s --output-directory %s"(gamma, buildPath("example", "hello-world.eag"), directory)
            .shouldPassWith("S grammar is single sweep");
        run!"cd %s && %s input"(directory, dotSlash("S"))
            .shouldPassWith("^Hello World!$");
    }
}

@("compile count1.eag as Single-Sweep and run compiler")
unittest
{
    with (sandbox)
    {
        run!"%s --sweep --space %s --output-directory %s"(gamma, buildPath("example", "count1.eag"), directory)
            .shouldPassWith("S grammar is single sweep");
        run!"cd %s && echo 1 1 1 1 1 1 1 1 1 1 1 1 1 | %s"(directory, dotSlash("S"))
            .shouldPassWith("^Number 1 3 $");
    }
}

@("compile count6.eag as Single-Sweep and run compiler")
unittest
{
    with (sandbox)
    {
        run!"%s --sweep %s --output-directory %s"(gamma, buildPath("example", "count6.eag"), directory)
            .shouldPassWith("S grammar is single sweep");
        run!"cd %s && echo a a a b b b | %s"(directory, dotSlash("S"))
            .shouldPassWith("^3$");
    }
}

@("compile decl-appl.eag as Single-Sweep and run compiler")
unittest
{
    with (sandbox)
    {
        run!"%s --sweep --space %s --output-directory %s"(gamma, buildPath("example", "decl-appl.eag"), directory)
            .shouldPassWith("DeclAppl grammar is single sweep");
        run!"cd %s && echo DECL ab DECL ba APPL ab | %s"(directory, dotSlash("DeclAppl"))
            .shouldPassWith("^ba ; ab ; $");
    }
}

@("compile single-sweep.eag as Single-Sweep and run compiler")
unittest
{
    with (sandbox)
    {
        run!"%s --sweep %s --output-directory %s"(gamma, buildPath("example", "single-sweep.eag"), directory)
            .shouldPassWith("S grammar is single sweep");
        run!"cd %s && echo a b c d e | %s"(directory, dotSlash("S"))
            .shouldPassWith("^$");
    }
}

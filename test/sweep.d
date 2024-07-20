module test.sweep;

import std.file;
import std.path;
import test.helper;

@("compile abc.eag as Single-Sweep and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --sweep --space %s --output-directory %s"(buildPath("example", "abc.eag"), directory)
            .shouldPassWith("S grammar is single sweep");
        run!"cd %s && echo a a a b b b c c c | ./S"(directory)
            .shouldPassWith(`^1 1 1 $`);
    }
}

@("compile ab.eag as Single-Sweep and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --sweep --space %s --output-directory %s"(buildPath("example", "ab.eag"), directory)
            .shouldPassWith("S grammar is single sweep");
        run!"cd %s && echo a a a b b b | ./S"(directory)
            .shouldPassWith("^1 1 1 $");
    }
}

@("compile bnf/ab.eag as Single-Sweep and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --sweep --space %s --output-directory %s"(buildPath("example", "bnf", "ab.eag"), directory)
            .shouldPassWith("S grammar is single sweep");
        run!"cd %s && echo a a a b b b | ./S"(directory)
            .shouldPassWith("^1 1 1 $");
    }
}

@("compile w-w.eag as Single-Sweep and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --sweep --space %s --output-directory %s"(buildPath("example", "w-w.eag"), directory)
            .shouldPassWith("S grammar is single sweep");
        run!"cd %s && echo a b a b c a b a b | ./S"(directory)
            .shouldPassWith("^a b a b $");
    }
}

@("compile hello-world.eag as Single-Sweep and run compiler")
unittest
{
    with (sandbox)
    {
        write(buildPath(directory, "input"), null);
        run!"./gamma --sweep %s --output-directory %s"(buildPath("example", "hello-world.eag"), directory)
            .shouldPassWith("S grammar is single sweep");
        run!"cd %s && ./S input"(directory)
            .shouldPassWith("^Hello World!$");
    }
}

@("compile count1.eag as Single-Sweep and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --sweep --space %s --output-directory %s"(buildPath("example", "count1.eag"), directory)
            .shouldPassWith("S grammar is single sweep");
        run!"cd %s && echo 1 1 1 1 1 1 1 1 1 1 1 1 1 | ./S"(directory)
            .shouldPassWith("^Number 1 3 $");
    }
}

@("compile count6.eag as Single-Sweep and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --sweep %s --output-directory %s"(buildPath("example", "count6.eag"), directory)
            .shouldPassWith("S grammar is single sweep");
        run!"cd %s && echo a a a b b b | ./S"(directory)
            .shouldPassWith("^3$");
    }
}

@("compile decl-appl.eag as Single-Sweep and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --sweep --space %s --output-directory %s"(buildPath("example", "decl-appl.eag"), directory)
            .shouldPassWith("DeclAppl grammar is single sweep");
        run!"cd %s && echo DECL ab DECL ba APPL ab | ./DeclAppl"(directory)
            .shouldPassWith("^ba ; ab ; $");
    }
}

@("compile single-sweep.eag as Single-Sweep and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --sweep %s --output-directory %s"(buildPath("example", "single-sweep.eag"), directory)
            .shouldPassWith("S grammar is single sweep");
        run!"cd %s && echo a b c d e | ./S"(directory)
            .shouldPassWith("^$");
    }
}

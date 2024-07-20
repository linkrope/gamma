module test.soag;

import core.exception;
import std.exception;
import std.file;
import std.path;
import test.helper;

@("compile abc.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --soag --space %s --output-directory %s"(buildPath("example", "abc.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo a a a b b b c c c | ./S"(directory)
            .shouldPassWith(`^1 1 1 $`);
    }
}

@("compile ab.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --soag --space %s --output-directory %s"(buildPath("example", "ab.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo a a a b b b | ./S"(directory)
            .shouldPassWith("^1 1 1 $");
    }
}

@("compile bnf/ab.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --soag --space %s --output-directory %s"(buildPath("example", "bnf", "ab.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo a a a b b b | ./S"(directory)
            .shouldPassWith("^1 1 1 $");
    }
}

@("compile w-w.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --soag --space %s --output-directory %s"(buildPath("example", "w-w.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo a b a b c a b a b | ./S"(directory)
            .shouldPassWith("^a b a b $");
    }
}

@("compile w-w-soag.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --soag --space %s --output-directory %s"(buildPath("example", "w-w-soag.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo a b a b c a b a b | ./S"(directory)
            .shouldPassWith("^a b a b $");
    }
}

@("compile hello-world.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        write(buildPath(directory, "input"), null);
        run!"./gamma --soag %s --output-directory %s"(buildPath("example", "hello-world.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && ./S input"(directory)
            .shouldPassWith("^Hello World!$");
    }
}

@("compile count1.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --soag --space %s --output-directory %s"(buildPath("example", "count1.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo 1 1 1 1 1 1 1 1 1 1 1 1 1 | ./S"(directory)
            .shouldPassWith("^Number 1 3 $");
    }
}

@("compile count2.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma %s --output-directory %s"(buildPath("example", "count2.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo a a a a a a a a a a a a a | ./S"(directory)
            .shouldPassWith("^13$");
    }
}

@("compile count3.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        write(buildPath(directory, "input"), null);
        run!"./gamma %s --output-directory %s"(buildPath("example", "count3.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && ./S input"(directory)
            .shouldPassWith("^0$");
    }
}

@("compile count4.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma %s --output-directory %s"(buildPath("example", "count4.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo a a a | ./S"(directory)
            .shouldPassWith("^3$");
    }
}

@("compile count5.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --soag %s --output-directory %s"(buildPath("example", "count5.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo a a a | ./S"(directory)
            .shouldPassWith("^3$");
    }
}

@("compile count6.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --soag %s --output-directory %s"(buildPath("example", "count6.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo a a a b b b | ./S"(directory)
            .shouldPassWith("^3$");
    }
}

@("compile decl-appl.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --soag --space %s --output-directory %s"(buildPath("example", "decl-appl.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo DECL ab DECL ba APPL ab | ./DeclAppl"(directory)
            .shouldPassWith("^ba ; ab ; $");
    }
}

@("compile example.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --soag %s --output-directory %s"(buildPath("example", "example.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo a b e 1 | ./P"(directory)
            .shouldPassWith("^1$");
    }
}

@("compile single-sweep.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --soag %s --output-directory %s"(buildPath("example", "single-sweep.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo a b c d e | ./S"(directory)
            .shouldPassWith("^$");
    }
}

@("compile single-sweep.eag as SOAG without optimization and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --soag -o %s --output-directory %s"(buildPath("example", "single-sweep.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo a b c d e | ./S"(directory)
            .shouldPassWith("^$");
    }
}

@("compile non-oag1.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma %s --output-directory %s"(buildPath("example", "non-oag1.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo b c | ./S"(directory)
            .shouldPassWith("^0$");
    }
}

@("compile non-oag2.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma %s --output-directory %s"(buildPath("example", "non-oag2.eag"), directory)
            .shouldPassWith(`grammar is SOAG \(backtracked\)`);
        run!"cd %s && echo b c c | ./S"(directory)
            .shouldPassWith("^0$");
    }
}

@("compile non-oag3.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma %s --output-directory %s"(buildPath("example", "non-oag3.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo b a a | ./S"(directory)
            .shouldPassWith("^0$");
    }
}

@("compile non-oag4.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma %s --output-directory %s"(buildPath("example", "non-oag4.eag"), directory)
            .shouldPassWith("grammar is SOAG");
        run!"cd %s && echo b a a | ./S"(directory)
            .shouldPassWith("^0$");
    }
}

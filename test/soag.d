module test.soag;

import core.exception;
import std.exception;
import std.stdio;
import test.helper;

@("compile abc.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --soag --space example/abc.eag --output-directory %s"(directory)
            .shouldMatch("grammar is SOAG");
        run!"cd %s && echo a a a b b b c c c | ./S"(directory)
            .shouldMatch(`^\| \| \| $`);
    }
}

@("compile ab.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --soag --space example/ab.eag --output-directory %s"(directory)
            .shouldMatch("grammar is SOAG");
        run!"cd %s && echo a a a b b b | ./S"(directory)
            .shouldMatch("^i i i $");
    }
}

@("compile ab.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --soag --space example/ab.eag --output-directory %s"(directory)
            .shouldMatch("grammar is SOAG");
        run!"cd %s && echo a a a b b b | ./S"(directory)
            .shouldMatch("^i i i $");
    }
}

@("compile w-w.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --soag --space example/w-w.eag --output-directory %s"(directory)
            .shouldMatch("grammar is SOAG");
        run!"cd %s && echo a b a b c a b a b | ./S"(directory)
            .shouldMatch("^a b a b $");
    }
}

@("compile w-w-soag.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --soag --space example/w-w-soag.eag --output-directory %s"(directory)
            .shouldMatch("grammar is SOAG");
        run!"cd %s && echo a b a b c a b a b | ./S"(directory)
            .shouldMatch("^a b a b $");
    }
}

@("compile hello-world.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --soag example/hello-world.eag --output-directory %s"(directory)
            .shouldMatch("grammar is SOAG");
        run!"cd %s && echo | ./S"(directory)
            .shouldMatch("^Hello World!$");
    }
}

@("compile count1.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --soag --space example/count1.eag --output-directory %s"(directory)
            .shouldMatch("grammar is SOAG");
        run!"cd %s && echo i i i i i i i i i i i i i | ./S"(directory)
            .shouldMatch("^Number 1 3 $");
    }
}

@("compile count2.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma example/count2.eag --output-directory %s"(directory)
            .shouldMatch("grammar is SOAG");
        run!"cd %s && echo a a a a a a a a a a a a a | ./S"(directory)
            .shouldMatch("^13$");
    }
}

@("compile count3.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma example/count3.eag --output-directory %s"(directory)
            .shouldMatch("grammar is SOAG");
        run!"cd %s && echo | ./S"(directory)
            .shouldMatch("^0$");
    }
}

@("compile count4.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma example/count4.eag --output-directory %s"(directory)
            .shouldMatch("grammar is SOAG");
        run!"cd %s && echo a a a | ./S"(directory)
            .shouldMatch("^3$");
    }
}

@("compile count5.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --soag example/count5.eag --output-directory %s"(directory)
            .shouldMatch("grammar is SOAG");
        run!"cd %s && echo a a a | ./S"(directory)
            .shouldMatch("^3$");
    }
}

@("compile count6.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --soag example/count6.eag --output-directory %s"(directory)
            .shouldMatch("grammar is SOAG");
        run!"cd %s && echo a a a b b b | ./S"(directory)
            .shouldMatch("^3$");
    }
}

@("compile decl-appl.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --soag --space example/decl-appl.eag --output-directory %s"(directory)
            .shouldMatch("grammar is SOAG");
        run!"cd %s && echo DECL ab DECL ba APPL ab | ./DeclAppl"(directory)
            .shouldMatch("^ba ; ab ; $");
    }
}

@("compile example.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --soag example/example.eag --output-directory %s"(directory)
            .shouldMatch("grammar is SOAG");
        run!"cd %s && echo a b e i | ./P"(directory)
            .shouldMatch("^i$");
    }
}

@("compile single-sweep.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --soag example/single-sweep.eag --output-directory %s"(directory)
            .shouldMatch("grammar is SOAG");
        run!"cd %s && echo a b c d e | ./S"(directory)
            .shouldMatch("^$");
    }
}

@("compile single-sweep.eag as SOAG without optimization and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --soag -o example/single-sweep.eag --output-directory %s"(directory)
            .shouldMatch("grammar is SOAG");
        run!"cd %s && echo a b c d e | ./S"(directory)
            .shouldMatch("^$");
    }
}

@("compile non-oag1.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma example/non-oag1.eag --output-directory %s"(directory)
            .shouldMatch("grammar is SOAG");
        run!"cd %s && echo b c | ./S"(directory)
            .shouldMatch("^0$");
    }
}

@("compile non-oag2.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma example/non-oag2.eag --output-directory %s"(directory)
            .shouldMatch(`grammar is SOAG \(backtracked\)`);
        run!"cd %s && echo b c c | ./S"(directory)
            .shouldMatch("^0$");
    }
}

@("compile non-oag3.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma example/non-oag3.eag --output-directory %s"(directory)
            .shouldMatch("grammar is SOAG");
        run!"cd %s && echo b a a | ./S"(directory)
            .shouldMatch("^0$");
    }
}

@("compile non-oag4.eag as SOAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma example/non-oag4.eag --output-directory %s"(directory)
            .shouldMatch("grammar is SOAG");
        run!"cd %s && echo b a a | ./S"(directory)
            .shouldMatch("^0$");
    }
}

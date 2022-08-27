module test.sweep;

import test.helper;

@("compile abc.eag as Single-Sweep and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --sweep --space example/abc.eag --output-directory %s"(directory)
            .shouldMatch("S grammar is single sweep");
        run!"cd %s && echo a a a b b b c c c | ./S"(directory)
            .shouldMatch(`^\| \| \| $`);
    }
}

@("compile ab.eag as Single-Sweep and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --sweep --space example/ab.eag --output-directory %s"(directory)
            .shouldMatch("S grammar is single sweep");
        run!"cd %s && echo a a a b b b | ./S"(directory)
            .shouldMatch("^i i i $");
    }
}

@("compile ab.eag as Single-Sweep and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --sweep --space example/ab.eag --output-directory %s"(directory)
            .shouldMatch("S grammar is single sweep");
        run!"cd %s && echo a a a b b b | ./S"(directory)
            .shouldMatch("^i i i $");
    }
}

@("compile w-w.eag as Single-Sweep and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --sweep --space example/w-w.eag --output-directory %s"(directory)
            .shouldMatch("S grammar is single sweep");
        run!"cd %s && echo a b a b c a b a b | ./S"(directory)
            .shouldMatch("^a b a b $");
    }
}

@("compile hello-world.eag as Single-Sweep and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --sweep example/hello-world.eag --output-directory %s"(directory)
            .shouldMatch("S grammar is single sweep");
        run!"cd %s && echo | ./S"(directory)
            .shouldMatch("^Hello World!$");
    }
}

@("compile count1.eag as Single-Sweep and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --sweep --space example/count1.eag --output-directory %s"(directory)
            .shouldMatch("S grammar is single sweep");
        run!"cd %s && echo i i i i i i i i i i i i i | ./S"(directory)
            .shouldMatch("^Number 1 3 $");
    }
}

@("compile count6.eag as Single-Sweep and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --sweep example/count6.eag --output-directory %s"(directory)
            .shouldMatch("S grammar is single sweep");
        run!"cd %s && echo a a a b b b | ./S"(directory)
            .shouldMatch("^3$");
    }
}

@("compile decl-appl.eag as Single-Sweep and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --sweep --space example/decl-appl.eag --output-directory %s"(directory)
            .shouldMatch("DeclAppl grammar is single sweep");
        run!"cd %s && echo DECL ab DECL ba APPL ab | ./DeclAppl"(directory)
            .shouldMatch("^ba ; ab ; $");
    }
}

@("compile single-sweep.eag as Single-Sweep and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --sweep example/single-sweep.eag --output-directory %s"(directory)
            .shouldMatch("S grammar is single sweep");
        run!"cd %s && echo a b c d e | ./S"(directory)
            .shouldMatch("^$");
    }
}

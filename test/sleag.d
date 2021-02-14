module test.sleag;

import test.helper;

@("compile abc.eag as SLEAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./epsilon --space example/abc.eag --output-directory %s"(directory)
            .shouldMatch("SLEAG testing S[^ ]* OK");
        run!"cd %s && echo a a a b b b c c c | ./S"(directory)
            .shouldMatch(`^\| \| \| $`);
    }
}

@("compile ab.eag as SLEAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./epsilon --space example/ab.eag --output-directory %s"(directory)
            .shouldMatch("SLEAG testing S[^ ]* OK");
        run!"cd %s && echo a a a b b b | ./S"(directory)
            .shouldMatch("^i i i $");
    }
}

@("compile ab-ebnf.eag as SLEAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./epsilon --space example/ab-ebnf.eag --output-directory %s"(directory)
            .shouldMatch("SLEAG testing S[^ ]* OK");
        run!"cd %s && echo a a a b b b | ./S"(directory)
            .shouldMatch("^i i i $");
    }
}

@("compile w-w.eag as SLEAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./epsilon --space example/w-w.eag --output-directory %s"(directory)
            .shouldMatch("SLEAG testing S[^ ]* OK");
        run!"cd %s && echo a b a b c a b a b | ./S"(directory)
            .shouldMatch("^a b a b $");
    }
}

@("compile hello-world.eag as SLEAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./epsilon example/hello-world.eag --output-directory %s"(directory)
            .shouldMatch("SLEAG testing S[^ ]* OK");
        run!"cd %s && echo | ./S"(directory)
            .shouldMatch("^Hello World!$");
    }
}

@("compile count1.eag as SLEAG and run compiler")
unittest
{
    with (sandbox)
    {
    run!"./epsilon --space example/count1.eag --output-directory %s"(directory)
        .shouldMatch("SLEAG testing S[^ ]* OK");
    run!"cd %s && echo i i i i i i i i i i i i i | ./S"(directory)
        .shouldMatch("^Number 1 3 $");
    }
}

@("compile count6.eag as SLEAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./epsilon example/count6.eag --output-directory %s"(directory)
            .shouldMatch("SLEAG testing S[^ ]* OK");
        run!"cd %s && echo a a a b b b | ./S"(directory)
            .shouldMatch("^3$");
    }
}

@("compile decl-appl.eag as SLEAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./epsilon --space example/decl-appl.eag --output-directory %s"(directory)
            .shouldMatch("SLEAG testing DeclAppl[^ ]* OK");
        run!"cd %s && echo DECL ab DECL ba APPL ab | ./DeclAppl"(directory)
            .shouldMatch("^ba ; ab ; $");
    }
}

@("compile ident-list.eag as SLEAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./epsilon --space example/ident-list.eag --output-directory %s"(directory)
            .shouldMatch("SLEAG testing S[^ ]* OK");
        run!"cd %s && echo ab ba | ./S"(directory)
            .shouldMatch("^ab ba $");
    }
}

@("compile lexer-test.eag as SLEAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./epsilon --space example/lexer-test.eag --output-directory %s"(directory)
            .shouldMatch("SLEAG testing ε[^ ]* OK");
        run!`cd %s && echo α β α β \\\\n α β β α| ./ε`(directory)
            .shouldMatch("^α α β β \n α α β β $");
    }
}

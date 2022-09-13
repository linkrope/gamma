module test.slag;

import test.helper;

@("compile abc.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --space example/abc.eag --output-directory %s"(directory)
            .shouldMatch("S grammar is SLAG");
        run!"cd %s && echo a a a b b b c c c | ./S"(directory)
            .shouldMatch(`^\| \| \| $`);
    }
}

@("compile ab.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --space example/ab.eag --output-directory %s"(directory)
            .shouldMatch("S grammar is SLAG");
        run!"cd %s && echo a a a b b b | ./S"(directory)
            .shouldMatch("^i i i $");
    }
}

@("compile ab.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --space example/ab.eag --output-directory %s"(directory)
            .shouldMatch("S grammar is SLAG");
        run!"cd %s && echo a a a b b b | ./S"(directory)
            .shouldMatch("^i i i $");
    }
}

@("compile w-w.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --space example/w-w.eag --output-directory %s"(directory)
            .shouldMatch("S grammar is SLAG");
        run!"cd %s && echo a b a b c a b a b | ./S"(directory)
            .shouldMatch("^a b a b $");
    }
}

@("compile hello-world.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma example/hello-world.eag --output-directory %s"(directory)
            .shouldMatch("S grammar is SLAG");
        run!"cd %s && echo | ./S"(directory)
            .shouldMatch("^Hello World!$");
    }
}

@("compile count1.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
    run!"./gamma --space example/count1.eag --output-directory %s"(directory)
        .shouldMatch("S grammar is SLAG");
    run!"cd %s && echo i i i i i i i i i i i i i | ./S"(directory)
        .shouldMatch("^Number 1 3 $");
    }
}

@("compile count6.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma example/count6.eag --output-directory %s"(directory)
            .shouldMatch("S grammar is SLAG");
        run!"cd %s && echo a a a b b b | ./S"(directory)
            .shouldMatch("^3$");
    }
}

@("compile decl-appl.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --space example/decl-appl.eag --output-directory %s"(directory)
            .shouldMatch("DeclAppl grammar is SLAG");
        run!"cd %s && echo DECL ab DECL ba APPL ab | ./DeclAppl"(directory)
            .shouldMatch("^ba ; ab ; $");
        run!"cd %s && echo DECL ab DECL ab | ./DeclAppl"(directory)
            .shouldFail("^error: predicate 'NotAlreadyDeclared' failed$");
        run!"cd %s && echo DECL ba APPL ab | ./DeclAppl"(directory)
            .shouldFail("^error: predicate 'Declared' failed$");
    }
}

@("compile expr.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --space example/expr.eag --output-directory %s"(directory)
            .shouldMatch("Expr grammar is SLAG");
        run!"cd %s && echo 1 + 0 + 1 | ./Expr"(directory)
            .shouldMatch("^1 ENTER 0 ENTER ADD 1 ENTER ADD $");
    }
}

@("compile ident-list.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --space example/ident-list.eag --output-directory %s"(directory)
            .shouldMatch("S grammar is SLAG");
        run!"cd %s && echo ab ba | ./S"(directory)
            .shouldMatch("^ab ba $");
    }
}

@("compile lexer-test.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --space example/lexer-test.eag --output-directory %s"(directory)
            .shouldMatch("ε grammar is SLAG");
        run!`cd %s && echo α β α β \\\\n α β β α| ./ε`(directory)
            .shouldMatch("^α α β β \n α α β β $");
    }
}

@("compile non-slag.eag")
unittest
{
    with (sandbox)
    {
        run!"./gamma example/non-slag.eag --output-directory %s"(directory)
            .shouldMatch("cannot analyze bottom up")
            .shouldMatch("cannot synthesize 2 times bottom up")
            .shouldMatch("cannot check for equality bottom up")
            .shouldMatch("cannot check for inequality bottom up")
            .shouldMatch("S grammar is no SLAG but LAG");
    }
}

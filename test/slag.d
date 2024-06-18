module test.slag;

import test.helper;

@("compile abc.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --space example/abc.eag --output-directory %s"(directory)
            .shouldPassWith("S grammar is SLAG");
        run!"cd %s && echo a a a b b b c c c | ./S"(directory)
            .shouldPassWith(`^1 1 1 $`);
    }
}

@("compile ab.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --space example/ab.eag --output-directory %s"(directory)
            .shouldPassWith("S grammar is SLAG");
        run!"cd %s && echo a a a b b b | ./S"(directory)
            .shouldPassWith("^1 1 1 $");
    }
}

@("compile ab.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --space example/ab.eag --output-directory %s"(directory)
            .shouldPassWith("S grammar is SLAG");
        run!"cd %s && echo a a a b b b | ./S"(directory)
            .shouldPassWith("^1 1 1 $");
    }
}

@("compile w-w.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --space example/w-w.eag --output-directory %s"(directory)
            .shouldPassWith("S grammar is SLAG");
        run!"cd %s && echo a b a b c a b a b | ./S"(directory)
            .shouldPassWith("^a b a b $");
    }
}

@("compile hello-world.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma example/hello-world.eag --output-directory %s"(directory)
            .shouldPassWith("S grammar is SLAG");
        run!"cd %s && echo | ./S"(directory)
            .shouldPassWith("^Hello World!$");
    }
}

@("compile count1.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
    run!"./gamma --space example/count1.eag --output-directory %s"(directory)
        .shouldPassWith("S grammar is SLAG");
    run!"cd %s && echo 1 1 1 1 1 1 1 1 1 1 1 1 1 | ./S"(directory)
        .shouldPassWith("^Number 1 3 $");
    }
}

@("compile count6.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma example/count6.eag --output-directory %s"(directory)
            .shouldPassWith("S grammar is SLAG");
        run!"cd %s && echo a a a b b b | ./S"(directory)
            .shouldPassWith("^3$");
    }
}

@("compile decl-appl.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --space example/decl-appl.eag --output-directory %s"(directory)
            .shouldPassWith("DeclAppl grammar is SLAG");
        run!"cd %s && echo DECL ab DECL ba APPL ab | ./DeclAppl"(directory)
            .shouldPassWith("^ba ; ab ; $");
        run!"cd %s && echo DECL ab DECL ab | ./DeclAppl"(directory)
            .shouldFailWith("^error: predicate 'NotAlreadyDeclared' failed$");
        run!"cd %s && echo DECL ba APPL ab | ./DeclAppl"(directory)
            .shouldFailWith("^error: predicate 'Declared' failed$");
    }
}

@("compile expr.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --space example/expr.eag --output-directory %s"(directory)
            .shouldPassWith("Expr grammar is SLAG");
        run!"cd %s && echo 1 + 0 + 1 | ./Expr"(directory)
            .shouldPassWith("^1 ENTER 0 ENTER ADD 1 ENTER ADD $");
    }
}

@("compile ident-list.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --space example/ident-list.eag --output-directory %s"(directory)
            .shouldPassWith("S grammar is SLAG");
        run!"cd %s && echo ab ba | ./S"(directory)
            .shouldPassWith("^ab ba $");
    }
}

version(Windows)
{
    // Unicode characters are not really supported on Windows command line...
}
else
{
    @("compile lexer-test.eag as SLAG and run compiler")
    unittest
    {
        with (sandbox)
        {
            run!"./gamma --space example/lexer-test.eag --output-directory %s"(directory)
                .shouldPassWith("ε grammar is SLAG");
            run!`cd %s && echo α β α β \\\\n α β β α| ./ε`(directory)
                .shouldPassWith("^α α β β \n α α β β $");
        }
    }
}

@("compile non-slag.eag")
unittest
{
    with (sandbox)
    {
        run!"./gamma example/non-slag.eag --output-directory %s"(directory)
            .shouldPassWith("cannot analyze bottom up")
            .shouldPassWith("cannot synthesize 2 times bottom up")
            .shouldPassWith("cannot check for equality bottom up")
            .shouldPassWith("cannot check for inequality bottom up")
            .shouldPassWith("S grammar is no SLAG but LAG");
    }
}

@("compile ebnf.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --space example/ebnf.eag --output-directory %s"(directory)
            .shouldPassWith("S grammar is SLAG");
        version(Windows)
        {
            run!`cd %s && echo a, , ab | ./S`(directory)
                .shouldPassWith("^a , , a b $");
            run!`cd %s && echo "a", "", "ab" | ./S`(directory)
                .shouldPassWith("^a , , a b $");
        }
        else
        {
            run!`cd %s && echo 'a, , ab' | ./S`(directory)
                .shouldPassWith("^a , , a b $");
            run!`cd %s && echo '"a", "", "ab"' | ./S`(directory)
                .shouldPassWith("^a , , a b $");
        }
    }
}

@("compile bnf/ebnf.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"./gamma --space example/bnf/ebnf.eag --output-directory %s"(directory)
            .shouldPassWith("S grammar is SLAG");
        version(Windows) 
        {
            run!`cd %s && echo a, , ab | ./S`(directory)
                .shouldPassWith("^a , , a b $");
            run!`cd %s && echo "a", "", "ab" | ./S`(directory)
                .shouldPassWith("^a , , a b $");
        }
        else
        {
            run!`cd %s && echo 'a, , ab' | ./S`(directory)
                .shouldPassWith("^a , , a b $");
            run!`cd %s && echo '"a", "", "ab"' | ./S`(directory)
                .shouldPassWith("^a , , a b $");
        }
    }
}

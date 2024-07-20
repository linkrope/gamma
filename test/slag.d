module test.slag;

import std.file;
import std.path;
import test.helper;

@("compile abc.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"%s --space %s --output-directory %s"(gamma, buildPath("example", "abc.eag"), directory)
            .shouldPassWith("S grammar is SLAG");
        run!"cd %s && echo a a a b b b c c c | %s"(directory, dotSlash("S"))
            .shouldPassWith(`^1 1 1 $`);
    }
}

@("compile ab.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"%s --space %s --output-directory %s"(gamma, buildPath("example", "ab.eag"), directory)
            .shouldPassWith("S grammar is SLAG");
        run!"cd %s && echo a a a b b b | %s"(directory, dotSlash("S"))
            .shouldPassWith("^1 1 1 $");
    }
}

@("compile bnf/ab.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"%s --space %s --output-directory %s"(gamma, buildPath("example", "bnf", "ab.eag"), directory)
            .shouldPassWith("S grammar is SLAG");
        run!"cd %s && echo a a a b b b | %s"(directory, dotSlash("S"))
            .shouldPassWith("^1 1 1 $");
    }
}

@("compile w-w.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"%s --space %s --output-directory %s"(gamma, buildPath("example", "w-w.eag"), directory)
            .shouldPassWith("S grammar is SLAG");
        run!"cd %s && echo a b a b c a b a b | %s"(directory, dotSlash("S"))
            .shouldPassWith("^a b a b $");
    }
}

@("compile hello-world.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        write(buildPath(directory, "input"), null);
        run!"%s %s --output-directory %s"(gamma, buildPath("example", "hello-world.eag"), directory)
            .shouldPassWith("S grammar is SLAG");
        run!"cd %s && %s input"(directory, dotSlash("S"))
            .shouldPassWith("^Hello World!$");
    }
}

@("compile count1.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"%s --space %s --output-directory %s"(gamma, buildPath("example", "count1.eag"), directory)
            .shouldPassWith("S grammar is SLAG");
        run!"cd %s && echo 1 1 1 1 1 1 1 1 1 1 1 1 1 | %s"(directory, dotSlash("S"))
            .shouldPassWith("^Number 1 3 $");
    }
}

@("compile count6.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"%s %s --output-directory %s"(gamma, buildPath("example", "count6.eag"), directory)
            .shouldPassWith("S grammar is SLAG");
        run!"cd %s && echo a a a b b b | %s"(directory, dotSlash("S"))
            .shouldPassWith("^3$");
    }
}

@("compile decl-appl.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"%s --space %s --output-directory %s"(gamma, buildPath("example", "decl-appl.eag"), directory)
            .shouldPassWith("DeclAppl grammar is SLAG");
        run!"cd %s && echo DECL ab DECL ba APPL ab | %s"(directory, dotSlash("DeclAppl"))
            .shouldPassWith("^ba ; ab ; $");
        run!"cd %s && echo DECL ab DECL ab | %s"(directory, dotSlash("DeclAppl"))
            .shouldFailWith("^error: predicate 'NotAlreadyDeclared' failed$");
        run!"cd %s && echo DECL ba APPL ab | %s"(directory, dotSlash("DeclAppl"))
            .shouldFailWith("^error: predicate 'Declared' failed$");
    }
}

@("compile expr.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"%s --space %s --output-directory %s"(gamma, buildPath("example", "expr.eag"), directory)
            .shouldPassWith("Expr grammar is SLAG");
        run!"cd %s && echo 1 + 0 + 1 | %s"(directory, dotSlash("Expr"))
            .shouldPassWith("^1 ENTER 0 ENTER ADD 1 ENTER ADD $");
    }
}

@("compile ident-list.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        run!"%s --space %s --output-directory %s"(gamma, buildPath("example", "ident-list.eag"), directory)
            .shouldPassWith("S grammar is SLAG");
        run!"cd %s && echo ab ba | %s"(directory, dotSlash("S"))
            .shouldPassWith("^ab ba $");
    }
}

version (Windows)
{
    pragma(msg, "skip lexer-test.eag because of missing Unicode support");
}
else
{
    @("compile lexer-test.eag as SLAG and run compiler")
    unittest
    {
        with (sandbox)
        {
            run!"%s --space %s --output-directory %s"(gamma, buildPath("example", "lexer-test.eag"), directory)
                .shouldPassWith("ε grammar is SLAG");
            run!`cd %s && echo α β α β \\\\n α β β α| %s`(directory, dotSlash("ε"))
                .shouldPassWith("^α α β β \n α α β β $");
        }
    }
}

@("compile non-slag.eag")
unittest
{
    with (sandbox)
    {
        run!"%s %s --output-directory %s"(gamma, buildPath("example", "non-slag.eag"), directory)
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
        write(buildPath(directory, "input"), `"a", "", "ab"`);
        run!"%s --space %s --output-directory %s"(gamma, buildPath("example", "ebnf.eag"), directory)
            .shouldPassWith("S grammar is SLAG");
        run!`cd %s && echo a, , ab | %s`(directory, dotSlash("S"))
            .shouldPassWith("^a , , a b $");
        run!`cd %s && %s input`(directory, dotSlash("S"))
            .shouldPassWith("^a , , a b $");
    }
}

@("compile bnf/ebnf.eag as SLAG and run compiler")
unittest
{
    with (sandbox)
    {
        write(buildPath(directory, "input"), `"a", "", "ab"`);
        run!"%s --space %s --output-directory %s"(gamma, buildPath("example", "bnf", "ebnf.eag"), directory)
            .shouldPassWith("S grammar is SLAG");
        run!`cd %s && echo a, , ab | %s`(directory, dotSlash("S"))
            .shouldPassWith("^a , , a b $");
        run!`cd %s && %s input`(directory, dotSlash("S"))
            .shouldPassWith("^a , , a b $");
    }
}

module test.sleag;

import test.helper;

@("compile abc.eag as SLEAG and run compiler")
unittest
{
    run("./epsilon --space example/abc.eag")
        .shouldMatch("SLEAG testing   S   ok");
    run("echo a a a b b b c c c | ./S")
        .shouldMatch(`^\| \| \| $`);
}

@("compile ab.eag as SLEAG and run compiler")
unittest
{
    run("./epsilon --space example/ab.eag")
        .shouldMatch("SLEAG testing   S   ok");
    run("echo a a a b b b | ./S")
        .shouldMatch("^i i i $");
}

@("compile ab-ebnf.eag as SLEAG and run compiler")
unittest
{
    run("./epsilon --space example/ab-ebnf.eag")
        .shouldMatch("SLEAG testing   S   ok");
    run("echo a a a b b b | ./S")
        .shouldMatch("^i i i $");
}

@("compile w-w.eag as SLEAG and run compiler")
unittest
{
    run("./epsilon --space example/w-w.eag")
        .shouldMatch("SLEAG testing   S   ok");
    run("echo a b a b c a b a b | ./S")
        .shouldMatch("^a b a b $");
}

@("compile hello-world.eag as SLEAG and run compiler")
unittest
{
    run("./epsilon example/hello-world.eag")
        .shouldMatch("SLEAG testing   S   ok");
    run("echo | ./S")
        .shouldMatch("^Hello World!$");
}

@("compile count1.eag as SLEAG and run compiler")
unittest
{
    run("./epsilon --space example/count1.eag")
        .shouldMatch("SLEAG testing   S   ok");
    run("echo i i i i i i i i i i i i i | ./S")
        .shouldMatch("^Number 1 3 $");
}

@("compile count6.eag as SLEAG and run compiler")
unittest
{
    run("./epsilon example/count6.eag")
        .shouldMatch("SLEAG testing   S   ok");
    run("echo a a a b b b | ./S")
        .shouldMatch("^3$");
}

@("compile decl-appl.eag as SLEAG and run compiler")
unittest
{
    run("./epsilon --space example/decl-appl.eag")
        .shouldMatch("SLEAG testing   DeclAppl   ok");
    run("echo DECL ab DECL ba APPL ab | ./DeclAppl")
        .shouldMatch("^ba ; ab ; $");
}

@("compile ident-list.eag as SLEAG and run compiler")
unittest
{
    run("./epsilon --space example/ident-list.eag")
        .shouldMatch("SLEAG testing   S   ok");
    run("echo ab ba | ./S")
        .shouldMatch("^ab ba $");
}

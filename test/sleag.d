module test.sleag;

import test.helper;

unittest
{
    run("./epsilon --space example/abc.eag")
        .shouldMatch("SLEAG testing   S   ok");
    run("echo a a a b b b c c c | ./S")
        .shouldMatch(`^\| \| \| $`);
}

unittest
{
    run("./epsilon --space example/ab.eag")
        .shouldMatch("SLEAG testing   S   ok");
    run("echo a a a b b b | ./S")
        .shouldMatch("^i i i $");
}

unittest
{
    run("./epsilon --space example/ab-ebnf.eag")
        .shouldMatch("SLEAG testing   S   ok");
    run("echo a a a b b b | ./S")
        .shouldMatch("^i i i $");
}

unittest
{
    run("./epsilon --space example/w-w.eag")
        .shouldMatch("SLEAG testing   S   ok");
    run("echo a b a b c a b a b | ./S")
        .shouldMatch("^a b a b $");
}

unittest
{
    run("./epsilon example/hello-world.eag")
        .shouldMatch("SLEAG testing   S   ok");
    run("echo | ./S")
        .shouldMatch("^Hello World!$");
}

unittest
{
    run("./epsilon --space example/count1.eag")
        .shouldMatch("SLEAG testing   S   ok");
    run("echo i i i i i i i i i i i i i | ./S")
        .shouldMatch("^Number 1 3 $");
}

unittest
{
    run("./epsilon example/count5.eag")
        .shouldMatch("SLEAG testing   S   ok");
    run("echo a a a b b b | ./S")
        .shouldMatch("^3$");
}

unittest
{
    run("./epsilon --space example/decl-appl.eag")
        .shouldMatch("SLEAG testing   DeclAppl   ok");
    run("echo DECL ab DECL ba APPL ab | ./DeclAppl")
        .shouldMatch("^ba ; ab ; $");
}

unittest
{
    run("./epsilon --space example/ident-list.eag")
        .shouldMatch("SLEAG testing   S   ok");
    run("echo ab ba | ./S")
        .shouldMatch("^ab ba $");
}

module test.sweep;

import test.helper;

unittest
{
    run("./epsilon --sweep --space example/abc.eag")
        .shouldMatch("SSweep testing S   ok");
    run("echo a a a b b b c c c | ./S")
        .shouldMatch(`^\| \| \| $`);
}

unittest
{
    run("./epsilon --sweep --space example/ab.eag")
        .shouldMatch("SSweep testing S   ok");
    run("echo a a a b b b | ./S")
        .shouldMatch("^i i i $");
}

unittest
{
    run("./epsilon --sweep --space example/ab-ebnf.eag")
        .shouldMatch("SSweep testing S   ok");
    run("echo a a a b b b | ./S")
        .shouldMatch("^i i i $");
}

unittest
{
    run("./epsilon --sweep --space example/w-w.eag")
        .shouldMatch("SSweep testing S   ok");
    run("echo a b a b c a b a b | ./S")
        .shouldMatch("^a b a b $");
}

unittest
{
    run("./epsilon --sweep example/hello-world.eag")
        .shouldMatch("SSweep testing S   ok");
    run("echo | ./S")
        .shouldMatch("^Hello World!$");
}

unittest
{
    run("./epsilon --sweep --space example/count1.eag")
        .shouldMatch("SSweep testing S   ok");
    run("echo i i i i i i i i i i i i i | ./S")
        .shouldMatch("^Number 1 3 $");
}

unittest
{
    run("./epsilon --sweep example/count5.eag")
        .shouldMatch("SSweep testing S   ok");
    run("echo a a a b b b | ./S")
        .shouldMatch("^3$");
}

unittest
{
    run("./epsilon --sweep --space example/decl-appl.eag")
        .shouldMatch("SSweep testing DeclAppl   ok");
    run("echo DECL ab DECL ba APPL ab | ./DeclAppl")
        .shouldMatch("^ba ; ab ; $");
}

unittest
{
    run("./epsilon --sweep example/single-sweep.eag")
        .shouldMatch("SSweep testing S   ok");
    run("echo a b c d e | ./S")
        .shouldMatch("^$");
}

module test.sweep;

import test.helper;

@("compile abc.eag as Single-Sweep and run compiler")
unittest
{
    run("./epsilon --sweep --space example/abc.eag")
        .shouldMatch("SSweep testing S   ok");
    run("echo a a a b b b c c c | ./S")
        .shouldMatch(`^\| \| \| $`);
}

@("compile ab.eag as Single-Sweep and run compiler")
unittest
{
    run("./epsilon --sweep --space example/ab.eag")
        .shouldMatch("SSweep testing S   ok");
    run("echo a a a b b b | ./S")
        .shouldMatch("^i i i $");
}

@("compile ab-ebnf.eag as Single-Sweep and run compiler")
unittest
{
    run("./epsilon --sweep --space example/ab-ebnf.eag")
        .shouldMatch("SSweep testing S   ok");
    run("echo a a a b b b | ./S")
        .shouldMatch("^i i i $");
}

@("compile w-w.eag as Single-Sweep and run compiler")
unittest
{
    run("./epsilon --sweep --space example/w-w.eag")
        .shouldMatch("SSweep testing S   ok");
    run("echo a b a b c a b a b | ./S")
        .shouldMatch("^a b a b $");
}

@("compile hello-world.eag as Single-Sweep and run compiler")
unittest
{
    run("./epsilon --sweep example/hello-world.eag")
        .shouldMatch("SSweep testing S   ok");
    run("echo | ./S")
        .shouldMatch("^Hello World!$");
}

@("compile count1.eag as Single-Sweep and run compiler")
unittest
{
    run("./epsilon --sweep --space example/count1.eag")
        .shouldMatch("SSweep testing S   ok");
    run("echo i i i i i i i i i i i i i | ./S")
        .shouldMatch("^Number 1 3 $");
}

@("compile count5.eag as Single-Sweep and run compiler")
unittest
{
    run("./epsilon --sweep example/count5.eag")
        .shouldMatch("SSweep testing S   ok");
    run("echo a a a b b b | ./S")
        .shouldMatch("^3$");
}

@("compile decl-appl.eag as Single-Sweep and run compiler")
unittest
{
    run("./epsilon --sweep --space example/decl-appl.eag")
        .shouldMatch("SSweep testing DeclAppl   ok");
    run("echo DECL ab DECL ba APPL ab | ./DeclAppl")
        .shouldMatch("^ba ; ab ; $");
}

@("compile single-sweep.eag as Single-Sweep and run compiler")
unittest
{
    run("./epsilon --sweep example/single-sweep.eag")
        .shouldMatch("SSweep testing S   ok");
    run("echo a b c d e | ./S")
        .shouldMatch("^$");
}

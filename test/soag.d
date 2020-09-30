module test.soag;

import core.exception;
import std.exception;
import std.stdio;
import test.helper;

@("compile abc.eag as SOAG and run compiler")
unittest
{
    run("./epsilon --soag --space example/abc.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo a a a b b b c c c | ./S")
        .shouldMatch(`^\| \| \| $`);
}

@("compile ab.eag as SOAG and run compiler")
unittest
{
    run("./epsilon --soag --space example/ab.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo a a a b b b | ./S")
        .shouldMatch("^i i i $");
}

@("compile ab-ebnf.eag as SOAG and run compiler")
unittest
{
    run("./epsilon --soag --space example/ab-ebnf.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo a a a b b b | ./S")
        .shouldMatch("^i i i $");
}

@("compile w-w.eag as SOAG and run compiler")
unittest
{
    run("./epsilon --soag --space example/w-w.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo a b a b c a b a b | ./S")
        .shouldMatch("^a b a b $");
}

@("compile w-w-soag.eag as SOAG and run compiler")
unittest
{
    run("./epsilon --soag --space example/w-w-soag.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo a b a b c a b a b | ./S")
        .shouldMatch("^a b a b $");
}

@("compile hello-world.eag as SOAG and run compiler")
unittest
{
    run("./epsilon --soag example/hello-world.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo | ./S")
        .shouldMatch("^Hello World!$");
}

@("compile count1.eag as SOAG and run compiler")
unittest
{
    run("./epsilon --soag --space example/count1.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo i i i i i i i i i i i i i | ./S")
        .shouldMatch("^Number 1 3 $");
}

@("compile count2.eag as SOAG and run compiler")
unittest
{
    run("./epsilon example/count2.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo a a a a a a a a a a a a a | ./S")
        .shouldMatch("^13$");
}

@("compile count3.eag as SOAG and run compiler")
unittest
{
    run("./epsilon example/count3.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo | ./S")
        .shouldMatch("^0$");
}

@("compile count4.eag as SOAG and run compiler")
unittest
{
    run("./epsilon example/count4.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo a a a | ./S")
        .shouldMatch("^3$");
}

@("compile count5.eag as SOAG and run compiler")
unittest
{
    run("./epsilon --soag example/count5.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo a a a b b b | ./S")
        .shouldMatch("^3$");
}

@("compile ecl-appl.eag as SOAG and run compiler")
unittest
{
    run("./epsilon --soag --space example/decl-appl.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo DECL ab DECL ba APPL ab | ./DeclAppl")
        .shouldMatch("^ba ; ab ; $");
}

@("compile example.eag as SOAG and run compiler")
unittest
{
    run("./epsilon --soag example/example.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo a b e i | ./P")
        .shouldMatch("^i$");
}

@("compile single-sweep.eag as SOAG and run compiler")
unittest
{
    run("./epsilon --soag example/single-sweep.eag")
        .shouldMatch("Grammar is SOEAG")
        .assertThrown!AssertError;
    writeln("    FAILED");
}

@("compile single-sweep.eag as SOAG without optimization and run compiler")
unittest
{
    run("./epsilon --soag -o example/single-sweep.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo a b c d e | ./S")
        .shouldMatch("^$");
}

@("compile not-oeag1.eag as SOAG and run compiler")
unittest
{
    run("./epsilon example/not-oeag1.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo b c | ./S")
        .shouldMatch("^0$");
}

@("compile not-oeag2.eag as SOAG and run compiler")
unittest
{
    run("./epsilon example/not-oeag2.eag")
        .shouldMatch(`Grammar is SOEAG \(backtracked\)`);
    run("echo b c c | ./S")
        .shouldMatch("^0$");
}

@("compile not-oeag3.eag as SOAG and run compiler")
unittest
{
    run("./epsilon example/not-oeag3.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo b a a | ./S")
        .shouldMatch("^0$");
}

@("compile not-oeag4.eag as SOAG and run compiler")
unittest
{
    run("./epsilon example/not-oeag4.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo b a a | ./S")
        .shouldMatch("^0$");
}

module test.soag;

import core.exception;
import std.exception;
import std.stdio;
import test.helper;

unittest
{
    run("./epsilon --soag --space example/abc.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo a a a b b b c c c | ./S")
        .shouldMatch(`^\| \| \| $`);
}

unittest
{
    run("./epsilon --soag --space example/ab.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo a a a b b b | ./S")
        .shouldMatch("^i i i $");
}

unittest
{
    run("./epsilon --soag --space example/ab-ebnf.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo a a a b b b | ./S")
        .shouldMatch("^i i i $");
}

unittest
{
    run("./epsilon --soag --space example/w-w.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo a b a b c a b a b | ./S")
        .shouldMatch("^a b a b $")
        .assertThrown!AssertError;
    writeln("    FAILED");
}

unittest
{
    run("./epsilon --soag --space example/w-w-soag.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo a b a b c a b a b | ./S")
        .shouldMatch("^a b a b $");
}

unittest
{
    run("./epsilon --soag example/hello-world.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo | ./S")
        .shouldMatch("^Hello World!$");
}

unittest
{
    run("./epsilon --soag --space example/count1.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo i i i i i i i i i i i i i | ./S")
        .shouldMatch("^Number 1 3 $");
}

unittest
{
    run("./epsilon example/count2.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo a a a a a a a a a a a a a | ./S")
        .shouldMatch("^13$");
}

unittest
{
    run("./epsilon example/count3.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo | ./S")
        .shouldMatch("^0$");
}

unittest
{
    run("./epsilon example/count4.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo a a a | ./S")
        .shouldMatch("^3$")
        .assertThrown!AssertError;
    writeln("    FAILED");
}

unittest
{
    run("./epsilon --soag example/count5.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo a a a b b b | ./S")
        .shouldMatch("^3$");
}

unittest
{
    run("./epsilon --soag --space example/decl-appl.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo DECL ab DECL ba APPL ab | ./DeclAppl")
        .shouldMatch("^ba ; ab ; $");
}

unittest
{
    run("./epsilon --soag example/example.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo a b e i | ./P")
        .shouldMatch("^i$");
}

unittest
{
    run("./epsilon --soag example/single-sweep.eag")
        .shouldMatch("Grammar is SOEAG")
        .assertThrown!AssertError;
    writeln("    FAILED");
}

unittest
{
    run("./epsilon --soag -o example/single-sweep.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo a b c d e | ./S")
        .shouldMatch("^$");
}

unittest
{
    run("./epsilon example/not-oeag1.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo b c | ./S")
        .shouldMatch("^0$");
}

unittest
{
    run("./epsilon example/not-oeag2.eag")
        .shouldMatch(`Grammar is SOEAG \(backtracked\)`);
    run("echo b c c | ./S")
        .shouldMatch("^0$");
}

unittest
{
    run("./epsilon example/not-oeag3.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo b a a | ./S")
        .shouldMatch("^0$");
}

unittest
{
    run("./epsilon example/not-oeag4.eag")
        .shouldMatch("Grammar is SOEAG");
    run("echo b a a | ./S")
        .shouldMatch("^0$");
}

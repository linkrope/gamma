module test.lalr;

import std.file : write;
import std.path : buildPath;
import test.helper;

@("compile left-recursion.eag and run LR parser")
unittest
{
    with (sandbox)
    {
        run!"%s --lalr --runtime . %s --output-directory %s"(
            gamma, buildPath("example", "left-recursion.eag"), directory)
            .shouldPassWith("LexGen writing S");
        write(buildPath(directory, "input"), "1 + 2 * 3");
        run!"cd %s && %s input"(directory, dotSlash("S"))
            .shouldPassWith("^OK$");
    }
}

@("compile left-recursion.eag and run LR parser on invalid input")
unittest
{
    with (sandbox)
    {
        run!"%s --lalr --runtime . %s --output-directory %s"(
            gamma, buildPath("example", "left-recursion.eag"), directory)
            .shouldPassWith("LexGen writing S");
        write(buildPath(directory, "input"), "2 ** 3");
        run!"cd %s && %s input"(directory, dotSlash("S"))
            .shouldFailWith(`error: Syntax error! Repairing input...\ninput:1:4`);
    }
}

@("compile decl-appl.eag and run LR parser")
unittest
{
    with (sandbox)
    {
        run!"%s --lalr --runtime . %s --output-directory %s"(
            gamma, buildPath("example", "decl-appl.eag"), directory)
            .shouldPassWith("LexGen writing DeclAppl");
        // current restriction: --lalr ignores `*`, so whitespace is accepted within `id*`
        write(buildPath(directory, "input"), "DECL a b APPL b a");
        run!"cd %s && %s input"(directory, dotSlash("DeclAppl"))
            .shouldPassWith("^OK$");
    }
}

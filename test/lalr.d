module test.lalr;

import std.file : write;
import std.path : buildPath;
import test.helper;

@("compile and run an LALR frontend on valid input")
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

@("LALR frontend rejects invalid input")
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

module test.lalr;

import std.path : buildPath;
import test.helper;

@("compile and run an LALR frontend on valid input")
unittest
{
    with (sandbox)
    {
        run!"%s --lalr %s --output-directory %s"(
            gamma, buildPath("example", "left-recursion.eag"), directory)
            .shouldPassWith("LexGen writing S");
        run!"cd %s && echo '1 + 2 * 3' | %s"(directory, dotSlash("S"))
            .shouldPassWith("^OK$");
    }
}

@("LALR frontend rejects invalid input")
unittest
{
    with (sandbox)
    {
        run!"%s --lalr %s --output-directory %s"(
            gamma, buildPath("example", "left-recursion.eag"), directory)
            .shouldPassWith("LexGen writing S");
        run!"cd %s && echo '2 ** 3' | %s"(directory, dotSlash("S"))
            .shouldFailWith(`error: Syntax error! Repairing input...\nstdin:1:4`);
    }
}

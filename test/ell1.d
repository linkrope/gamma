module test.ell1;

import std.path;
import test.helper;

@("compile left-recursion.eag")
unittest
{
    with (sandbox)
    {
        run!"%s %s --output-directory %s"(gamma, buildPath("example", "left-recursion.eag"), directory)
            .shouldFailWith("left recursion");
    }
}

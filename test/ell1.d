module test.ell1;

import std.path;
import test.helper;

@("compile left-recursion.eag")
unittest
{
    with (sandbox)
    {
        run!"./gamma %s --output-directory %s"(buildPath("example", "left-recursion.eag"), directory)
            .shouldFailWith("left recursion");
    }
}

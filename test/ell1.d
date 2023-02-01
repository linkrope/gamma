module test.ell1;

import test.helper;

@("compile left-recursion.eag")
unittest
{
    with (sandbox)
    {
        run!"./gamma example/left-recursion.eag --output-directory %s"(directory)
            .shouldFailWith("left recursion");
    }
}

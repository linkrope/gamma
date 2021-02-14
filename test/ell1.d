module test.ell1;

import test.helper;

@("compile left-recursion.eag")
unittest
{
    with (sandbox)
    {
        run!"./epsilon example/left-recursion.eag --output-directory %s"(directory)
            .shouldFail("left recursion");
    }
}

module test.ell1;

import std.string;
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

@("issue #11: ensure trailing content before EOF is reported as syntax error by LL(1) parser")
unittest
{
    with (sandbox)
    {
        const eag = `
            N = | '1' N.

            S<+  : N>:
                .
            S<+ '1' N: N>: 
                'a' S<N> 'b'.
            `.outdent;

        run!"cat <<EOF | ./gamma --output-directory %s%sEOF"(directory, eag)
            .shouldPassWith("S grammar is SLAG");
        run!"cd %s && echo aa bbb | ./S"(directory)
            .shouldFailWith("error: syntax error, unexpected content before end of file");
    }
}

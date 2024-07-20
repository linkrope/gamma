module test.issues;

import std.file;
import std.path;
import std.string;
import test.helper;

@("issue #1: grammar with unproductive start symbol")
unittest
{
    with (sandbox)
    {
        const name = buildPath(directory, "test.eag");
        const eag = `
            S = .

            S <+ : S>: A.
            A: 'a' A.
            `.outdent;

        write(name, eag);
        run!"%s --output-directory %s %s"(gamma, directory, name)
            .shouldFailWith("error: start symbol S is unproductive");
    }
}

@("issue #1: grammar with unproductive symbol but productive start symbol")
unittest
{
    with (sandbox)
    {
        const name = buildPath(directory, "test.eag");
        const eag = `
            S = .

            S <+ : S>: A | 'b'.
            A: 'a' A.
            `.outdent;

        write(name, eag);
        run!"%s --output-directory %s %s"(gamma, directory, name)
            .shouldPassWith("warn: A is unproductive");
    }
}

@("issue #11: do not silently skip trailing content")
unittest
{
    with (sandbox)
    {
        const name = buildPath(directory, "test.eag");
        const eag = `
            N = | '1' N.

            S<+  : N>:
                .
            S<+ '1' N: N>:
                'a' S<N> 'b'.
            `.outdent;

        write(name, eag);
        run!"%s --output-directory %s %s"(gamma, directory, name)
            .shouldPassWith("S grammar is SLAG");
        run!"cd %s && echo aa bbb | %s"(directory, dotSlash("S"))
            .shouldFailWith("syntax error, end expected");
    }
}

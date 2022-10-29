module test.issues;

import std.string;
import test.helper;

@("issue #1: grammar with unproductive start symbol")
unittest
{
    with (sandbox)
    {
        const eag = `
            S = .

            S <+ : S>: A.
            A: 'a' A.
            `.outdent;

        run!"cat <<EOF | ./gamma --output-directory %s%sEOF"(directory, eag)
            .shouldFailWith("error: start symbol S is unproductive");
    }
}

@("issue #1: grammar with unproductive symbol but productive start symbol")
unittest
{
    with (sandbox)
    {
        const eag = `
            S = .

            S <+ : S>: A | 'b'.
            A: 'a' A.
            `.outdent;

        run!"cat <<EOF | ./gamma --output-directory %s%sEOF"(directory, eag)
            .shouldPassWith("warn: A is unproductive");
    }
}

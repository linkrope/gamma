module test.lexical_vertical_slice;

import std.path : buildPath;
import std.string : outdent, strip;
import test.helper;

@("compile the canonical lexical vertical-slice grammar as LALR")
unittest
{
    /+
    const input = ` \t< <=(*(* *)*)if ifx<=`;
    const expectedTokens = `
        terminal '<'
        terminal '<='
        terminal 'if'
        rule id  ifx
        terminal '<='
        end
        `.outdent.strip;
    +/

    with (sandbox)
    {
        run!"%s --lalr -g %s --output-directory %s"(
            gamma, buildPath("example", "lexical-vertical-slice.eag"), directory)
            .shouldPassWith("LexGen writing S");
    }

    // Step 3 will run `input` through the generated lex-only executable and
    // compare its deterministic output with `expectedTokens`.
}

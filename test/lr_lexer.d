module test.lr_lexer;

import std.file : write;
import std.path : buildPath;
import test.helper;

@("trace terminal-only LALR lexer tokens from the generated compiler")
unittest
{
    with (sandbox)
    {
        run!"%s --lalr --runtime . %s --output-directory %s"(
            gamma, buildPath("example", "lr-lexer-test.eag"), directory)
            .shouldPassWith("Linking S");
        write(buildPath(directory, "input"), " \t< <=(*(**)*)if x <=");
        run!"cd %s && %s --verbose input"(directory, dotSlash("S"))
            .shouldPassWith(
                "trace: LR lexer terminal '<'",
                "trace: LR lexer terminal '<='",
                "trace: LR lexer terminal 'if'",
                "trace: LR lexer terminal 'x'",
            );
    }
}


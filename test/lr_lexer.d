module test.lr_lexer;

import std.file : write;
import std.path : buildPath;
import test.helper;

@("trace lexer terminals and lexical nonterminals")
unittest
{
    with (sandbox)
    {
        run!"%s --lalr --runtime . %s --output-directory %s"(
            gamma, buildPath("example", "lr-lexer-test.eag"), directory)
            .shouldPassWith("Linking S");
        write(buildPath(directory, "input"), " \t< <=(*(**)*)if ifif");
        run!"cd %s && %s --verbose input"(directory, dotSlash("S"))
            .shouldPassWith(
                "trace: lexer terminal '<'",
                "trace: lexer terminal '<='",
                "trace: lexer terminal 'if'",
                "trace: lexer nonterminal id",
            );
    }
}

@("parse a spaced identifier while ignoring lexical nonterminals")
unittest
{
    with (sandbox)
    {
        run!"%s --lalr -p --space --runtime . %s --output-directory %s"(
            gamma, buildPath("example", "decl-appl.eag"), directory)
            .shouldPassWith("DeclAppl grammar is single sweep");
        write(buildPath(directory, "input"), "DECL a b APPL a b");
        run!"cd %s && %s input"(directory, dotSlash("DeclAppl"))
            .shouldPassWith("^OK$");
    }
}

@("delete a lexer error during LR parser repair")
unittest
{
    with (sandbox)
    {
        run!"%s --lalr --runtime . %s --output-directory %s"(
            gamma, buildPath("example", "lr-lexer-test.eag"), directory)
            .shouldPassWith("Linking S");
        write(buildPath(directory, "input"), "@ifif");
        run!"cd %s && %s --verbose input"(directory, dotSlash("S"))
            .shouldFailWith(
                "trace: lexer error",
                "info: Deleting unknown token",
                "trace: lexer nonterminal id",
            );
    }
}

@("reject ambiguous lexical nonterminals")
unittest
{
    with (sandbox)
    {
        const grammar = `
            S = .

            S <+ : S>: a.

            a*: 'x'.

            b*: 'x'.
            `;

        const fileName = buildPath(directory, "ambiguous.eag");

        write(fileName, grammar);
        run!"%s --lalr --runtime . %s --output-directory %s"(gamma, fileName, directory)
            .shouldFailWith("error: ambiguous lexical nonterminals a and b");
    }
}

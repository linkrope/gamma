module test.lr_lexer;

import std.file : write;
import std.path : buildPath;
import std.string : outdent, strip;
import test.helper;

@("trace LR lexer precedence, whitespace, and comments from generated compiler")
unittest
{
    with (sandbox)
    {
        const parseTree = `
            trace: digraph ParseTree {
              node [shape=box];
              n0 [label="S"];
              n1 [label="_1"];
              n2 [label="'if'"];
              n1 -> n2;
              n3 [label="_1"];
              n4 [label="op"];
              n5 [label="'<'"];
              n4 -> n5;
              n3 -> n4;
              n6 [label="_1"];
              n7 [label="op"];
              n8 [label="'<='"];
              n7 -> n8;
              n6 -> n7;
              n9 [label="_1"];
              n10 [label="id"];
              n11 [label="id"];
              n12 [label="id"];
              n13 [label="id"];
              n14 [label="letter"];
              n15 [label="'i'"];
              n14 -> n15;
              n13 -> n14;
              n12 -> n13;
              n16 [label="letter"];
              n17 [label="'f'"];
              n16 -> n17;
              n12 -> n16;
              n11 -> n12;
              n18 [label="letter"];
              n19 [label="'i'"];
              n18 -> n19;
              n11 -> n18;
              n10 -> n11;
              n20 [label="letter"];
              n21 [label="'f'"];
              n20 -> n21;
              n10 -> n20;
              n9 -> n10;
              n22 [label="_1"];
              n23 [label="ε"];
              n22 -> n23;
              n9 -> n22;
              n6 -> n9;
              n3 -> n6;
              n1 -> n3;
              n0 -> n1;
            }
            `.outdent.strip;

        run!"%s --lalr --runtime . %s --output-directory %s"(
                gamma, buildPath("example", "lr-lexer-test.eag"), directory)
            .shouldPassWith("S grammar is single sweep");
        // \u2003 is Unicode EM SPACE, exercising non-ASCII whitespace boundaries.
        // The nested comment contains U+1F600 GRINNING FACE to show that its content is ignored.
        write(buildPath(directory, "input"), "\u2003if<\u2003<=(*(*\U0001F600*)*)ifif");
        run!"cd %s && %s --verbose input"(directory, dotSlash("S"))
            .shouldPassWith(
                    "trace: lexer terminal 'if'",
                    "trace: lexer terminal '<'",
                    "trace: lexer terminal '<='",
                    "trace: lexer nonterminal id",
                    parseTree.escape,
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

@("repair lexical error without evaluation")
unittest
{
    with (sandbox)
    {
        run!"%s --lalr --runtime . %s --output-directory %s"(
                gamma, buildPath("example", "lr-lexer-test.eag"), directory)
            .shouldPassWith("S grammar is single sweep");
        write(buildPath(directory, "input"), "@ifif");
        auto result = run!"cd %s && %s --verbose input"(directory, dotSlash("S"));

        result.shouldFailWith(
                "error: unknown token",
                "input:1:1",
                `error: Syntax error! Repairing input...`.escape,
                "info: Deleting unknown token",
                "trace: lexer nonterminal id",
        );
    }
}

@("reject nullable lexical nonterminal")
unittest
{
    with (sandbox)
    {
        const grammar = `
            S = .

            S <+ : S>: a.

            a*: ['a'].
            `;

        const fileName = buildPath(directory, "nullable-lexical-nonterminal.eag");

        write(fileName, grammar);
        run!"%s --lalr --runtime . %s --output-directory %s"(gamma, fileName, directory)
            .shouldFailWith("error: nullable lexical nonterminal a");
    }
}

@("repair unterminated nested comment")
unittest
{
    with (sandbox)
    {
        run!"%s --lalr --runtime . %s --output-directory %s"(
                gamma, buildPath("example", "lr-lexer-test.eag"), directory)
            .shouldPassWith("S grammar is single sweep");
        write(buildPath(directory, "input"), "(*(*)");
        auto result = run!"cd %s && %s --verbose input"(directory, dotSlash("S"));

        result.shouldFailWith(
                "error: comment not closed at end of text",
                "input:1:1",
                `error: Syntax error! Repairing input...`.escape,
                "info: End of parsing",
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

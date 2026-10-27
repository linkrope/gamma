module test.lalr;

import std.file : write;
import std.path : buildPath;
import std.string;
import test.helper;

@("compile left-recursion.eag and run LR parser")
unittest
{
    with (sandbox)
    {
        const parseTree = `
            trace: digraph ParseTree {
              node [shape=box];
              n0 [label="S"];
              n1 [label="expr"];
              n2 [label="expr"];
              n3 [label="term"];
              n4 [label="factor"];
              n5 [label="number"];
              n6 [label="digit"];
              n7 [label="'1'"];
              n6 -> n7;
              n5 -> n6;
              n4 -> n5;
              n3 -> n4;
              n2 -> n3;
              n1 -> n2;
              n8 [label="_2"];
              n9 [label="'+'"];
              n8 -> n9;
              n1 -> n8;
              n10 [label="term"];
              n11 [label="factor"];
              n12 [label="number"];
              n13 [label="digit"];
              n14 [label="'2'"];
              n13 -> n14;
              n12 -> n13;
              n11 -> n12;
              n10 -> n11;
              n1 -> n10;
              n0 -> n1;
            }
            `.outdent.strip;

        run!"%s --lalr --runtime . %s --output-directory %s"(
            gamma, buildPath("example", "left-recursion.eag"), directory)
            .shouldPassWith("LexGen writing S");
        write(buildPath(directory, "input"), "1 + 2");
        run!"cd %s && %s --verbose input"(directory, dotSlash("S"))
            .shouldPassWith(parseTree.escape);
    }
}

@("compile left-recursion.eag and run LR parser on invalid input")
unittest
{
    with (sandbox)
    {
        const parseTree = `
            trace: digraph ParseTree {
              node [shape=box];
              n0 [label="S"];
              n1 [label="expr"];
              n2 [label="term"];
              n3 [label="term"];
              n4 [label="term"];
              n5 [label="factor"];
              n6 [label="number"];
              n7 [label="digit"];
              n8 [label="'2'"];
              n7 -> n8;
              n6 -> n7;
              n5 -> n6;
              n4 -> n5;
              n3 -> n4;
              n9 [label="_4"];
              n10 [label="'*'"];
              n9 -> n10;
              n3 -> n9;
              n11 [label="factor"];
              n12 [label="number"];
              n13 [label="digit"];
              n14 [label="'0'"];
              n13 -> n14;
              n12 -> n13;
              n11 -> n12;
              n3 -> n11;
              n2 -> n3;
              n15 [label="_4"];
              n16 [label="'*'"];
              n15 -> n16;
              n2 -> n15;
              n17 [label="factor"];
              n18 [label="number"];
              n19 [label="digit"];
              n20 [label="'3'"];
              n19 -> n20;
              n18 -> n19;
              n17 -> n18;
              n2 -> n17;
              n1 -> n2;
              n0 -> n1;
            }
            `.outdent.strip;

        run!"%s --lalr --runtime . %s --output-directory %s"(
            gamma, buildPath("example", "left-recursion.eag"), directory)
            .shouldPassWith("LexGen writing S");
        write(buildPath(directory, "input"), "2 ** 3");
        run!"cd %s && %s --verbose input"(directory, dotSlash("S"))
            .shouldFailWith(
                `error: Syntax error! Repairing input...`.escape,
                `info: Inserting '0'`,
                parseTree.escape,
            );
    }
}

@("compile decl-appl.eag and run LR parser")
unittest
{
    with (sandbox)
    {
        run!"%s --lalr --runtime . %s --output-directory %s"(
            gamma, buildPath("example", "decl-appl.eag"), directory)
            .shouldPassWith("LexGen writing DeclAppl");
        // current restriction: --lalr ignores `*`, so whitespace is accepted within `id*`
        write(buildPath(directory, "input"), "DECL a b APPL b a");
        run!"cd %s && %s input"(directory, dotSlash("DeclAppl"))
            .shouldPassWith("^OK$");
    }
}

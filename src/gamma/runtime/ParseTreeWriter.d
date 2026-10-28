module gamma.runtime.ParseTreeWriter;

import gamma.runtime.lr.LR1ParserTables : Symbol;
import gamma.runtime.ParseTree;
import std.format : format;
import std.range;
import std.sumtype : get, match;

/**
 * Writes a parse tree as deterministic GraphViz DOT.
 */
public struct ParseTreeWriter
{
    private const string[size_t] terminalNames;

    private const string[size_t] nonterminalNames;

    private size_t nextNode;

    public this(const Symbol[] terminals, const Symbol[] nonterminals)
    {
        import std.algorithm : map;
        import std.array : assocArray;
        import std.typecons : tuple;

        this.terminalNames = terminals
            .map!(symbol => tuple(cast(size_t) symbol.index, symbol.name))
            .assocArray;
        this.nonterminalNames = nonterminals
            .map!(symbol => tuple(cast(size_t) symbol.index, symbol.name))
            .assocArray;
    }

    public string write(const ParseTree tree)
    {
        import std.array : appender;

        auto result = appender!string;

        result.put("digraph ParseTree {\n  node [shape=box];\n");
        this.nextNode = 0;
        writeNode(result, tree.root);
        result.put("}\n");

        return result[];
    }

    private size_t writeNode(Writer)(ref Writer writer, const(ParseNode)* node)
    if (isOutputRange!(Writer, char))
    {
        const nodeNumber = this.nextNode++;
        const label = (*node).match!(node => label(node));

        writer.put(format!"  n%s [label=\"%s\"];\n"(nodeNumber, label.escape));

        (*node).match!(
            (const RuleNode ruleNode)
            {
                if (ruleNode.children.empty)
                {
                    const childNumber = this.nextNode++;

                    writer.put(format!"  n%s [label=\"ε\"];\n"(childNumber));
                    writer.put(format!"  n%s -> n%s;\n"(nodeNumber, childNumber));
                }

                foreach (child; ruleNode.children)
                {
                    const childNumber = writeNode(writer, child);

                    writer.put(format!"  n%s -> n%s;\n"(nodeNumber, childNumber));
                }
            },
            (_) {}
        );

        return nodeNumber;
    }

    private string label(const TerminalNode terminalNode)
    {
        auto name = terminalNode.terminal in this.terminalNames;

        assert(name !is null);
        return *name;
    }

    private string label(const RuleNode ruleNode)
    {
        auto name = ruleNode.lhs in this.nonterminalNames;

        assert(name !is null);
        return *name;
    }
}

@("render parse trees as deterministic DOT")
unittest
{
    import io : UndefPos;
    import std.string : outdent, strip;

    auto a = new ParseNode(TerminalNode(1, UndefPos));
    auto b = new ParseNode(TerminalNode(3, UndefPos));
    auto empty = new ParseNode(RuleNode(4, 2, [], UndefPos));
    auto aSb = new ParseNode(RuleNode(4, 1, [a, empty, b], UndefPos));
    auto tree = ParseTree(aSb, UndefPos);
    auto writer = ParseTreeWriter(
        [Symbol(1, "a"), Symbol(3, "b")],
        [Symbol(4, "S")]);

    const expected = `
        digraph ParseTree {
          node [shape=box];
          n0 [label="S"];
          n1 [label="a"];
          n0 -> n1;
          n2 [label="S"];
          n3 [label="ε"];
          n2 -> n3;
          n0 -> n2;
          n4 [label="b"];
          n0 -> n4;
        }
        `.outdent.strip;

    assert(writer.write(tree).strip == expected);
}

private string escape(string value)
{
    import std.string : replace;

    return value.replace(`\`, `\\`).replace(`"`, `\"`).replace("\n", `\n`);
}

@("escape special characters")
unittest
{
    assert(escape(`"` ~ `\`) == `\"\\`);
    assert(escape("\n") == `\n`);
}

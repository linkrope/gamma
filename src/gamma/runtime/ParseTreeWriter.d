module gamma.runtime.ParseTreeWriter;

import gamma.runtime.ParseTree;
import std.array : appender;
import std.format : format;
import std.range : isOutputRange, put;
import std.sumtype : get, match;

/**
 * Writes a parse tree as deterministic GraphViz DOT.
 */
public struct ParseTreeWriter
{
    private string[] terminalRepresentations;

    private string[] ruleLhsRepresentations;

    private size_t nextNode;

    public this(string[] terminalRepresentations, string[] ruleLhsRepresentations)
    {
        this.terminalRepresentations = terminalRepresentations.dup;
        this.ruleLhsRepresentations = ruleLhsRepresentations.dup;
    }

    public string write(const ParseTree tree)
    {
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
        const label = (*node).match!(
            (const Terminal terminal) => terminalLabel(terminal),
            (const Rule rule) => ruleLabel(rule),
        );

        writer.put(format!"  n%s [label=\"%s\"];\n"(nodeNumber, label.escape));

        (*node).match!(
            (const Rule rule)
            {
                foreach (child; rule.children)
                {
                    const childNumber = writeNode(writer, child);

                    writer.put(format!"  n%s -> n%s;\n"(nodeNumber, childNumber));
                }
            },
            (_) {}
        );

        return nodeNumber;
    }

    private string terminalLabel(const Terminal terminal)
    in (terminal.terminal < this.terminalRepresentations.length)
    {
        return this.terminalRepresentations[terminal.terminal];
    }

    private string ruleLabel(const Rule rule)
    in (rule.ruleAlt < this.ruleLhsRepresentations.length)
    {
        return this.ruleLhsRepresentations[rule.ruleAlt];
    }
}

private string escape(string value)
{
    import std.string : replace;

    return value.replace(`\`, `\\`).replace(`"`, `\"`).replace("\n", `\n`);
}

@("render parse trees as deterministic DOT")
unittest
{
    import io : UndefPos;
    import std.string : outdent, strip;

    auto terminal = new ParseNode(Terminal(0, UndefPos));
    auto root = new ParseNode(Rule(0, [terminal], UndefPos));
    auto tree = ParseTree(root, UndefPos);
    auto writer = ParseTreeWriter(["a\"\\"], ["Start"]);

    const expected = `
        digraph ParseTree {
          node [shape=box];
          n0 [label="Start"];
          n1 [label="a\"\\"];
          n0 -> n1;
        }
        `.outdent.strip;

    assert(writer.write(tree).strip == expected);
}

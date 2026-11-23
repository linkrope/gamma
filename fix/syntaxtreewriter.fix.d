module $;

import gamma.runtime.SyntaxTree : root, tree;
import std.array : Appender, appender;
import std.format : format;
import std.range : put;
import std.string : replace;

public struct SyntaxTreeWriter
{
    private size_t nextNode;

    public string write()
    {
        auto result = appender!string;

        result.put("digraph SyntaxTree {\n  node [shape=box];\n");
        this.nextNode = 0;
        $(result, root);
        result.put("}\n");

        return result[];
    }

    $
}

private string escape(string value)
{
    return value.replace(`\`, `\\`).replace(`"`, `\"`).replace("\n", `\n`);
}
$

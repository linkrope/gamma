module gamma.parsgen.lalr1.QuotedTerminalRecognizerWriter;

import std.array : array;
import std.format : format;
import std.range : empty;
import std.string : join;
import std.utf : byDchar;

/**
 * Writes a direct quoted-terminal recognizer as a prefix trie in generated D code.
 */
public string writeQuotedTerminalRecognizer(const string[] terminalNames)
{
    auto root = new TrieNode;

    root.stateIndex = 0;

    foreach (terminal, name; terminalNames)
    {
        if (name.empty)
            continue;

        auto node = root;
        foreach (character; name[1 .. $ - 1].byDchar)
            node = node.child(character);
        if (node.terminal == size_t.max)
            node.terminal = terminal;
    }

    TrieNode[] nodes = [root];

    size_t nodeIndex = 0;

    while (nodeIndex < nodes.length)
    {
        foreach (character; nodeCharacters(nodes[nodeIndex]))
        {
            auto child = nodes[nodeIndex].children[character];

            if (child.stateIndex == size_t.max)
            {
                child.stateIndex = nodes.length;
                nodes ~= child;
            }
        }
        ++nodeIndex;
    }

    string[] lines = [
        "private Nullable!QuotedTerminalCandidate quotedTerminalCandidate(Input input)",
        "{",
        "    Input cursor = input;",
        "    Nullable!QuotedTerminalCandidate result;",
        "",
    ];

    foreach (node; nodes)
        writeNode(lines, node);

    lines ~= "}";
    return lines.join("\n") ~ "\n";
}

private class TrieNode
{
    size_t stateIndex = size_t.max;

    size_t terminal = size_t.max;

    TrieNode[dchar] children;

    public TrieNode child(dchar character)
    {
        if (auto result = character in children)
            return *result;

        auto result = new TrieNode;

        children[character] = result;
        return result;
    }
}

private void writeNode(ref string[] lines, TrieNode node)
{
    lines ~= format!"state%s:"(node.stateIndex);
    if (node.terminal != size_t.max)
        lines ~= format!"    result = QuotedTerminalCandidate(%s, cursor).nullable;"(node.terminal);
    lines ~= [
        "    if (cursor.empty)",
        "        return result;",
        "",
        "    switch (cursor.front)",
        "    {",
    ];

    foreach (character; nodeCharacters(node))
    {
        const child = node.children[character];

        lines ~= format!"    case cast(dchar) 0x%08x:"(character);
        lines ~= "        cursor.popFront;";
        lines ~= format!"        goto state%s;"(child.stateIndex);
    }

    lines ~= [
        "    default:",
        "        return result;",
        "    }",
        "",
    ];
}

private dchar[] nodeCharacters(TrieNode node)
{
    import std.algorithm : sort;

    return node.children.keys.array.sort.array;
}

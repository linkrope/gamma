module gamma.parsgen.TerminalRecognizerWriter;

import gamma.parsgen.FixWriter : includeFix;
import gamma.parsgen.SourceWriter : indent;
import io : Input;
import std.array : array;
import std.format : format;
import std.range : empty;
import std.stdio : File;
import std.string : outdent, stripLeft;
import std.utf : byDchar;

/**
 * Writes a terminal recognizer as a prefix trie in generated D code.
 */
public void writeTerminalRecognizer(File output, const string[] terminalNames)
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

    enum fixName = "terminalrecognizer.fix.d";
    Input fix = Input(fixName, import(fixName));

    includeFix(fix, output, '$', fixName);
    foreach (node; nodes)
        writeNode(output, node);
    includeFix(fix, output, '$', fixName);
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

private void writeNode(File output, TrieNode node)
{
    output.write(format!(`
        state%s:
        `.outdent.stripLeft)(node.stateIndex));
    if (node.terminal != size_t.max)
        output.write(format!(`
            result = TerminalCandidate(%s, cursor).nullable;
            `.outdent.stripLeft)(node.terminal).indent!4);
    output.write(
        `
        if (cursor.empty)
            return result;

        switch (cursor.front)
        {
        `.outdent.stripLeft.indent!4);

    foreach (character; nodeCharacters(node))
    {
        const child = node.children[character];

        output.write(format!(`
            case cast(dchar) 0x%08x:
                cursor.popFront;
                goto state%s;
            `.outdent.stripLeft)(character, child.stateIndex).indent!4);
    }

    output.write(
        `
        default:
            return result;
        }

        `.outdent.stripLeft.indent!4);
}

private dchar[] nodeCharacters(TrieNode node)
{
    import std.algorithm : sort;

    return node.children.keys.array.sort.array;
}

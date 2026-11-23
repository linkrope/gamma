module gamma.parsgen.SourceWriter;

/**
 * Adds indentation to nonblank lines of generated source.
 */
public string indent(size_t width)(string text)
{
    import std.array : appender, replicate;
    import std.string : splitLines;
    import std.typecons : Yes;

    enum indentation = " ".replicate(width);
    auto result = appender!string;

    foreach (line; text.splitLines(Yes.keepTerminator))
    {
        if (line != "\n")
            result.put(indentation);
        result.put(line);
    }
    return result.data;
}

@("indent generated source without indenting blank lines")
unittest
{
    import std.string : outdent, stripLeft;

    const source = `
        first;

        second;
        `.outdent.stripLeft;

    assert(source.indent!4 == "    first;\n\n    second;\n");
}

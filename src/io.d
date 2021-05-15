module io;

import std.range;
import std.stdio;

Input read(string name)
{
    return read(name, File(name));
}

Input read(string name, File file)
{
    import std.algorithm : joiner;
    import std.array : array;

    auto text = cast(char[]) file.byChunk(4096).joiner.array;

    return Input(name, text);
}

struct Input
{
    private string name;

    private const(char)[] text;

    private size_t index_;

    private size_t begin;

    private size_t line = 1;

    private size_t col = 1;

    private size_t offset; // needed by the Epsilon language server for marking problems

    this(string name, const(char)[] text) @nogc nothrow
    {
        this.name = name;
        this.text = text;
    }

    void popFront()
    in (!empty)
    {
        import std.utf : stride;

        const lineBreak = front == '\n';

        if (lineBreak)
        {
            ++line;
            col = 0;
        }
        index_ += text[index_ .. $].stride;
        ++offset;
        ++col;
        if (lineBreak)
            begin = index_;
    }

    dchar front() const
    {
        return empty ? 0 : text[index_ .. $].front;
    }

    bool empty() const @nogc nothrow
    {
        return text[index_ .. $].empty;
    }

    Position position() const pure @safe
    {
        import std.algorithm : find;

        const end = text.length - text[begin .. $].find('\n').length;

        return Position(name, line, col, offset, text[begin .. end]);
    }

    const(char)[] sliceFrom(size_t begin) const @nogc nothrow
    in (begin <= index)
    {
        return text[begin .. index_];
    }

    size_t index() const @nogc nothrow
    {
        return index_;
    }
}

const UndefPos = Position();

struct Position
{
    private string name;

    private size_t line;

    private size_t col;

    private size_t offset; // needed by the Epsilon language server for marking problems

    private const(char)[] text;

    string toString() const @safe
    {
        import std.array : appender;

        auto writer = appender!string;

        toString(writer);
        return writer[];
    }

    void toString(W)(ref W writer) const
    if (isOutputRange!(W, char))
    {
        import std.algorithm : map;
        import std.format : format;
        import std.utf : count;

        if (this == UndefPos)
        {
            writer.put("unknown position");
            return;
        }

        const link = format!"%s:%s:%s"(name, line, col);

        writer.put(link);
        writer.put(' ');
        writer.put(text);
        writer.put('\n');
        writer.put(' ');
        writer.put(' '.repeat(link.count));
        writer.put(text.take(col - 1).map!(c => (c == '\t') ? c : ' '));
        writer.put('^');
    }

    /*
     * Reports a position with an offset in the form <file-name>@<offset> instead of line and column.
     * This is a machine interface for allowing the Epslion language server to add markers via the offset. 
     */
    string toStringWithOffset() const @safe
    {
        import std.array : appender;

        auto writer = appender!string;

        toStringWithOffset(writer);
        return writer[];
    }

    void toStringWithOffset(W)(ref W writer) const
    if (isOutputRange!(W, char))
    {
        import std.algorithm : map;
        import std.format : format;

        if (this == UndefPos)
        {
            const link = format!"%s@0:1:1"(name);
            writer.put(link);
        }
        else {
            const link = format!"%s@%s:%s:%s"(name, offset, line, col);
            writer.put(link);
        }

    }

}

@("convert position to string")
unittest
{
    import std.string : outdent, strip;

    const position = Position("äöü.txt", 42, 2, 47, "äöü");
    const expected = `
        äöü.txt:42:2 äöü
                      ^
        `.outdent.strip;

    assert(position.toString == expected);
}

@("convert unknown position to string")
unittest
{
    import std.string : outdent, strip;

    const expected = `
        unknown position
        `.outdent.strip;

    assert(UndefPos.toString == expected);
}

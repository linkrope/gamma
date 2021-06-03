module io;

import std.range;
import std.stdio;
import std.typecons;

Input read(string name, Flag!"offset" offset = No.offset)
{
    return read(name, File(name), offset);
}

Input read(string name, File file, Flag!"offset" offset = No.offset)
{
    import std.algorithm : joiner;
    import std.array : array;

    auto text = cast(char[]) file.byChunk(4096).joiner.array;

    return Input(name, text, offset);
}

struct Input
{
    private string name;

    private const(char)[] text;

    private size_t index_;

    private size_t begin;

    private size_t line = 1;

    private size_t col = 1; // offset, for offset-based positions

    private Flag!"offset" offset;

    this(string name, const(char)[] text, Flag!"offset" offset = No.offset) @nogc nothrow
    {
        this.name = name;
        this.text = text;
        this.offset = offset;
        if (offset)
            line = col = 0;
    }

    void popFront()
    in (!empty)
    {
        import std.utf : stride;

        const lineBreak = front == '\n';

        if (lineBreak && !offset)
        {
            ++line;
            col = 0;
        }
        index_ += text[index_ .. $].stride;
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

        return Position(name, line, col, text[begin .. end]);
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

    private size_t col; // offset, if line is 0

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

        if (line == 0) // offset position
        {
            const link = format!"%s@%s"(name, col);

            writer.put(link);
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
}

@("convert position to string")
unittest
{
    import std.string : outdent, strip;

    const position = Position("äöü.txt", 42, 2, "äöü");
    const expected = `
        äöü.txt:42:2 äöü
                      ^
        `.outdent.strip;

    assert(position.toString == expected);
}

@("convert offset position to string")
unittest
{
    import std.string : outdent, strip;

    const position = Position("äöü.txt", 0, 42, "äöü");
    const expected = `
        äöü.txt@42
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

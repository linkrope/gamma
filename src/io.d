module io;

import std.range;
import std.stdio;
import std.typecons : Flag;

Input read(string name, bool useOffset = false)
{
    return read(name, File(name), useOffset);
}

Input read(string name, File file, bool useOffset = false)
{
    import std.algorithm : joiner;
    import std.array : array;

    auto text = cast(char[]) file.byChunk(4096).joiner.array;

    return Input(name, text, useOffset);
}

struct Input
{
    private string name;

    private const(char)[] text;

    private size_t index_;

    private size_t begin;

    private size_t line;

    private size_t col; // holds the offset if useOffset is true, column otherwise

    private bool useOffset;

    this(string name, const(char)[] text, bool useOffset = false) @nogc nothrow
    {
        this.name = name;
        this.text = text;
        this.useOffset = useOffset;
        if (useOffset) 
        {
            this.line = 0;
            this.col = 0;
        }
        else 
        {
            this.line = 1;
            this.col = 1;
        }
    }

    void popFront()
    in (!empty)
    {
        import std.utf : stride;

        const lineBreak = front == '\n';

        if (lineBreak && !useOffset)
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
        if (useOffset) {    
            return Position(name, 0, col, "");
        }
        else {
            import std.algorithm : find;

            const end = text.length - text[begin .. $].find('\n').length;

            return Position(name, line, col, text[begin .. end]);
        }
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

    private size_t col; // if line is 0 then this holds the offset (in case of LS support)

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
        if (this == UndefPos)
        {
            writer.put("unknown position");
            return;
        }

        import std.format : format;
        if (line == 0) // means, useOffset == true 
        {    
            const link = format!"%s@%s"(name, col);
            writer.put(link);
        }
        else {
            import std.algorithm : map;
            import std.utf : count;

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

    const position = Position("äöü.txt", 0, 43, "äöü");
    const expected = `
        äöü.txt@43
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

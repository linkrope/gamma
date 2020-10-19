module io;

import std.range;
import std.stdio;

Input read(string name)
{
    return read(name, File(name));
}

Input read(string name, File file)
{
    char[] text;
    char[] buffer;

    while (file.readln(buffer))
        text ~= buffer;
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

    this(string name, const(char)[] text)
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
        ++col;
        if (lineBreak)
            begin = index_;
    }

    dchar front() const
    {
        return empty ? 0 : text[index_ .. $].front;
    }

    bool empty() const
    {
        return text[index_ .. $].empty;
    }

    Position position() const
    {
        import std.algorithm : find;

        const end = text.length - text[begin .. $].find('\n').length;

        return Position(name, line, col, text[begin .. end]);
    }

    const(char)[] sliceFrom(size_t begin) const
    in (begin <= index)
    {
        return text[begin .. index_];
    }

    size_t index() const
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

    private const(char)[] text;

    string toString() const
    {
        import std.array : appender;

        auto writer = appender!string;

        toString(writer);
        return writer.data;
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

@("convert unknown position to string")
unittest
{
    import std.string : outdent, strip;

    const expected = `
        unknown position
        `.outdent.strip;

    assert(UndefPos.toString == expected);
}

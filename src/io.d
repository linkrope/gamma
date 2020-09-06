module io;

import std.range;
import std.stdio;

struct TextIn
{
    string name;

    char[] text;

    size_t index;

    size_t begin;

    size_t line = 1;

    size_t col = 1;

    this(string name)
    {
        this(name, File(name));
    }

    this(string name, File file)
    {
        char[] buffer;

        this.name = name;
        while (file.readln(buffer))
            text ~= buffer;
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
        index += text[index .. $].stride;
        ++col;
        if (lineBreak)
            begin = index;
    }

    dchar front() const
    {
        return empty ? 0 : text[index .. $].front;
    }

    bool empty() const
    {
        return text[index .. $].empty;
    }

    Position position() const
    {
        import std.algorithm : find;

        const end = text.length - text[begin .. $].find('\n').length;

        return Position(name, line, col, text[begin .. end]);
    }
}

const UndefPos = Position();

struct Position
{
    string name;

    size_t line;

    size_t col;

    const(char)[] text;

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

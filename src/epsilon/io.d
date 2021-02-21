module epsilon.io;

import log;
import runtime;
import std.stdio;

const optCh1 = '\\';
const optCh2 = '-';
const standardCompileOpts = 's';
bool[char] option;
bool[char][char] longOption;
string[] files;

TextOut Msg;

class TextOut
{
    string name;

    File file;

    this(string name)
    {
        this.name = name;
        this(File(name, "w"));
    }

    this(File file)
    {
        this.file = file;
    }

    void write(string s) @safe
    {
        file.write(s);
    }

    void write(char[] s)
    {
        import std.string : fromStringz;

        file.write(fromStringz(s.ptr));
    }

    void write(char c) @safe
    {
        file.write(c);
    }

    void write(long i) @safe
    {
        import std.conv : to;

        file.write(i.to!string);
    }

    void writeln() @safe
    {
        file.writeln;
    }

    void flush() @safe
    {
        file.flush;
    }
}

void CloseOut(ref TextOut Out) @safe
{
    Out.flush;
    Out = null;
}

void Show(TextOut Out) @safe
{
    import std.file : readText;

    write(readText!(char[])(Out.name));
}

void Compile(TextOut Out) @safe
{
    info!"compile %s"(Out.name);
    files = Out.name ~ files;
}

void OpenFile(ref File F, string name) @safe
{
    F = File(name, "r");
}

void CreateFile(ref File F, string name) @safe
{
    F = File(name, "w");
}

void CloseFile(ref File F) @safe
{
    F.close;
}

void GetLInt(File F, ref long i)
{
    F.readf!"long %s\n"(i);
}

void GetSet(File F, ref size_t s)
{
    F.readf!"set %s\n"(s);
}

void PutLInt(File F, long i) @safe
{
    F.writefln!"long %s"(i);
}

void PutSet(File F, size_t s) @safe
{
    F.writefln!"set %s"(s);
}

long TimeStamp() @nogc nothrow @safe
{
    import core.time : MonoTime;

    return MonoTime.currTime.ticks;
}

static this()
{
    Msg = new TextOut(stdout);
    Msg.name = "System.Log";
}

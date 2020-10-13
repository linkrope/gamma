module eIO;

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

    void write(string s)
    {
        file.write(s);
    }

    void write(char[] s)
    {
        import std.string : fromStringz;

        file.write(fromStringz(s.ptr));
    }

    void write(char c)
    {
        file.write(c);
    }

    void write(long i)
    {
        import std.conv : to;

        file.write(i.to!string);
    }

    void writeln()
    {
        file.writeln;
    }

    void flush()
    {
        file.flush;
    }
}

void CloseOut(ref TextOut Out)
{
    Out.flush;
    Out = null;
}

void Show(TextOut Out)
{
    import std.file : readText;

    write(readText!(char[])(Out.name));
}

void Compile(TextOut Out)
{
    info!"compile %s"(Out.name);
    files = Out.name ~ files;
}

void OpenFile(ref File F, string name, ref bool Error)
{
    // TODO: error handling
    F = File(name, "r");
}

void CreateFile(ref File F, string name)
{
    F = File(name, "w");
}

void CloseFile(ref File F)
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

void PutLInt(File F, long i)
{
    F.writefln!"long %s"(i);
}

void PutSet(File F, size_t s)
{
    F.writefln!"set %s"(s);
}

long TimeStamp()
{
    import core.time : MonoTime;

    return MonoTime.currTime.ticks;
}

static this()
{
    Msg = new TextOut(stdout);
    Msg.name = "System.Log";
}

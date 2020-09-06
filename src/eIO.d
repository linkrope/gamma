module eIO;

import runtime;
import std.stdio;

const eol = '\n';
const optCh1 = '\\';
const optCh2 = '-';
const standardCompileOpts = 's';
bool[char] option;
bool[char][char] longOption;
string[] files;

class TextIn
{
    char[] text;
    long offset;

    this(File file)
    {
        char[] buffer;

        while (file.readln(buffer))
            this.text ~= buffer;
    }
}

class TextOut
{
    string Name;
    File file;

    this(string name)
    {
        this.Name = name;
        this(File(name, "w"));
    }

    this(File file)
    {
        this.file = file;
    }
}

TextOut Msg;

void OpenIn(ref TextIn In, string Name, ref bool Error)
{
    // TODO: error handling
    In = new TextIn(File(Name));
}

void CloseIn(ref TextIn In)
{
    In = null;
}

void Read(TextIn In, ref char c)
{
    if (In.offset >= In.text.length)
    {
        c = 0;
        return;
    }
    c = In.text[In.offset];
    ++In.offset;
}

void CreateModOut(ref TextOut Out, char[] Name)
{
    import std.string : fromStringz;

    const name = fromStringz(Name.ptr).idup ~ ".d";

    CreateOut(Out, name);
}

void CreateOut(ref TextOut Out, string Name)
{
    Out = new TextOut(Name);
}

void Update(TextOut Out)
{
    Out.file.flush;
}

void CloseOut(ref TextOut Out)
{
    Update(Out);
    Out = null;
}

void Show(TextOut Out)
{
    import std.file : readText;

    write(readText!(char[])(Out.Name));
}

void WriteText(TextOut Out, string Str)
{
    Out.file.write(Str);
}

void WriteText(TextOut Out, char[] Str)
{
    import std.string : fromStringz;

    Out.file.write(fromStringz(Str.ptr));
    // TODO: escaping
    /+
    int i;
    char c;
    i = 0;
    c = Str[0];
    while (c != '\x00')
    {
        if (c == '\\')
        {
            ++i;
            c = Str[i];
            switch (c)
            {
            case '\x00':
                return;
                break;
            case '\'':
                Texts.Write(Out.W, '"');
                break;
            case 't':
                Texts.Write(Out.W, '\x09');
                break;
            case 'n':
                Texts.Write(Out.W, eol);
                break;
            default:
                Texts.Write(Out.W, c);
            }
        }
        else
        {
            Texts.Write(Out.W, c);
        }
        ++i;
        c = Str[i];
    }
    +/
}

void WriteString(T)(TextOut Out, T Str)
{
    WriteText(Out, Str);
}

void Write(TextOut Out, char c)
{
    Out.file.write(c);
}

void WriteInt(TextOut Out, long i)
{
    Out.file.writef!"%d"(i);
}

void WriteIntF(TextOut Out, long i, int Len)
{
    Out.file.writef!"%*d"(Len, i);
}

void WriteLn(TextOut Out)
{
    Out.file.writeln;
}

void Compile(TextOut Out, ref bool Error)
{
    writeln;
    files = Out.Name ~ files;
}

void OpenFile(ref File F, string Name, ref bool Error)
{
    // TODO: error handling
    F = File(Name, "r");
}

void CreateFile(ref File F, char[] Name)
{
    import std.string : fromStringz;

    F = File(fromStringz(Name.ptr), "w");
}

void CloseFile(ref File F)
{
    F.close;
}

void GetLInt(File F, ref long i)
{
    F.readf!"long %s\n"(i);
}

void GetSet(File F, ref uint s)
{
    F.readf!"set %s\n"(s);
}

void PutLInt(File F, long i)
{
    F.writefln!"long %s"(i);
}

void PutSet(File F, uint s)
{
    F.writefln!"set %s"(s);
}

long TimeStamp()
{
    import core.time : MonoTime;

    return MonoTime.currTime.ticks;
}

bool IsOption(char c1)
{
    return option.get(c1, false);
}

bool IsLongOption(char c1, char c2)
{
    return longOption.get(c1, null).get(c2, false);
}

static this()
{
    Msg = new TextOut(stdout);
    // Msg.Txt = Oberon.Log;
    // Texts.OpenWriter(Msg.W);
    Msg.Name = "System.Log";
}

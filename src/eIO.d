module eIO;

import runtime;
import Texts;
// import TextFrames;
// import Viewers;
// import MenuViewers;
// import Oberon;
import Files;
// import Compiler;

const eol = '\n';
const optCh1 = '\\';
const optCh2 = '-';
const standardCompileOpts = 's';
bool[char] option;

struct Position
{
    long Offset;
}

class TextIn
{
    import std.stdio : File;

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
    import std.stdio : File;

    string Name;
    File file;
    char[] text;
    bool IsShown;

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

class File
{
    Files.Rider Rider;
    bool NewFile;
}

TextOut Msg;
Position UndefPos;
Texts.Reader ParamReader;
char ParamCh;

void OpenIn(ref TextIn In, string Name, ref bool Error)
{
    import std.stdio : File;

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

void Pos(TextIn In, ref Position Pos)
{
    Pos = Position(In.offset);
}

void PrevPos(TextIn In, ref Position Pos)
{
    Pos = Position(In.offset - 1);
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
    Out.file.write(Out.text);
    Out.file.flush;
    Out.text = null;
}

void CloseOut(ref TextOut Out)
{
    Update(Out);
    Out = null;
}

void Show(TextOut Out)
{
    import std.file : readText;
    import std.stdio : write;

    write(readText!(char[])(Out.Name));
}

void WriteText(TextOut Out, string Str)
{
    Out.text ~= Str;
}

void WriteText(TextOut Out, char[] Str)
{
    import std.string : fromStringz;

    Out.text ~= fromStringz(Str.ptr);
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
    Out.text ~= c;
}

void WriteInt(TextOut Out, long i)
{
    import std.format : format;

    Out.text ~= format!"%d"(i);
}

void WriteIntF(TextOut Out, long i, int Len)
{
    import std.format : format;

    Out.text ~= format!"%*d"(Len, i);
}

void WritePos(TextOut Out, Position Pos)
{
    WriteString(Out, "pos ");
    WriteIntF(Out, Pos.Offset, 6);
}

void WriteLn(TextOut Out)
{
    Out.text ~= '\n';
}

void Compile(TextOut Out, ref bool Error)
{
    import std.stdio : writefln;

    writefln!"\nTODO: compile %s"(Out.Name);
}

void OpenFile(ref File F, string Name, ref bool Error)
{
    assert(false, "not implemented");
    /+
    Files.File File;
    File = Files.Old(Name);
    if (File !is null)
    {
        NEW(F);
        Files.Set(F.Rider, File, 0);
        F.NewFile = false;
        Error = false;
    }
    else
    {
        F = null;
        Error = true;
    }
    +/
}

void CreateFile(ref File F, char[] Name)
{
    assert(false, "not implemented");
    /+
    NEW(F);
    if (Name != "")
    {
        Files.Set(F.Rider, Files.New(Name), 0);
    }
    else
    {
        Files.Set(F.Rider, Files.New("IOFilStd.Bin"), 0);
    }
    F.NewFile = true;
    +/
}

void CloseFile(ref File F)
{
    assert(false, "not implemented");
    /+
    Files.Close(Files.Base(F.Rider));
    if (F.NewFile)
    {
        Files.Register(Files.Base(F.Rider));
    }
    F = null;
    +/
}

void GetLInt(File F, ref long i)
{
    assert(false, "not implemented");
    /+
    Files.ReadLInt(F.Rider, i);
    +/
}

void GetSet(File F, ref uint s)
{
    assert(false, "not implemented");
    /+
    Files.ReadSet(F.Rider, s);
    +/
}

void PutLInt(File F, long i)
{
    assert(false, "not implemented");
    /+
    Files.WriteLInt(F.Rider, i);
    +/
}

void PutSet(File F, uint s)
{
    assert(false, "not implemented");
    /+
    Files.WriteSet(F.Rider, s);
    +/
}

long TimeStamp()
{
    assert(false, "not implemented");
    /+
    return Oberon.Time();
    +/
}

void NextParam(ref string String)
{
    assert(false, "not implemented");
    /+
    long i;
    while (ParamCh <= " " && ParamCh != '\x00')
    {
        Texts.Read(ParamReader, ParamCh);
    }
    i = 0;
    while (i < String.length - 1 && ParamCh > " ")
    {
        String[i] = ParamCh;
        Texts.Read(ParamReader, ParamCh);
        ++i;
    }
    String[i] = '\x00';
    +/
}

void FirstParam(ref string String)
{
    assert(false, "not implemented");
    /+
    Texts.OpenReader(ParamReader, Oberon.Par.text, Oberon.Par.pos);
    Texts.Read(ParamReader, ParamCh);
    NextParam(String);
    +/
}

bool IsOption(char c1)
{
    return option.get(c1, false);
}

bool IsLongOption(char c1, char c2)
{
    string String;
    int i;
    char c;
    if (c1 < 'a' || 'z' < c1)
    {
        return false;
    }
    else if (c2 < 'A' || 'Z' < c2)
    {
        return false;
    }
    FirstParam(String);
    while (String[0] == optCh1 || String[0] == optCh2)
    {
        i = 1;
        c = String[1];
        while ('A' <= c && c <= 'Z' || 'a' <= c && c <= 'z')
        {
            if (c == c1 && String[i + 1] == c2)
            {
                return true;
            }
            ++i;
            c = String[i];
        }
        NextParam(String);
    }
    return false;
}

void NumOption(ref long Num)
{
    string String;
    int i;
    int d;
    char c;
    Num = 0;
    FirstParam(String);
    while (String[0] == optCh1 || String[0] == optCh2)
    {
        i = 1;
        c = String[1];
        if ('0' <= c && c <= '9')
        {
            do
            {
                d = ORD(c) - ORD('0');
                if (Num <= DIV(long.max - d, 10))
                {
                    Num = Num * 10 + d;
                }
                else
                {
                    Num = long.max;
                }
                ++i;
                c = String[i];
            }
            while (!(c < '0' || '9' < c));
            return;
        }
        NextParam(String);
    }
}

void StringOption(ref char[] Str)
{
    string String;
    int i;
    char c;
    Str[0] = '\x00';
    FirstParam(String);
    while (String[0] == optCh1 || String[0] == optCh2)
    {
        if (String[1] == '"')
        {
            i = 2;
            c = String[2];
            while (c != '"' && c != '\x00' && i < Str.length + 1)
            {
                Str[i - 2] = c;
                ++i;
                c = String[i];
            }
            if (c == '"')
            {
                Str[i - 2] = '\x00';
            }
            else
            {
                Str[0] = '\x00';
            }
            return;
        }
        NextParam(String);
    }
}

void InputName(ref string Name)
{
    FirstParam(Name);
    while (Name[0] == optCh1 || Name[0] == optCh2)
    {
        NextParam(Name);
    }
}

static this()
{
    import std.stdio : stdout;

    Msg = new TextOut(stdout);
    // Msg.Txt = Oberon.Log;
    // Texts.OpenWriter(Msg.W);
    Msg.Name = "System.Log";
    Msg.IsShown = true;
    UndefPos.Offset = -1;
}

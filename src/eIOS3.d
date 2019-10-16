module eIO;
import runtime;
import Display;
import Texts;
import TextFrames;
import Viewers;
import MenuViewers;
import Oberon;
import TextDocs;
import Files;
import Compiler;

const eol = '\x0d';
const optCh1 = "\\";
const optCh2 = "-";
const standardCompileOpts = "s";
class Position
{
    long Offset;
}

class TextIn
{
    Texts.Reader R;
}

class TextOut
{
    char[33] Name;
    Texts.Text Txt;
    Texts.Writer W;
    bool IsShown;
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
void OpenIn(ref TextIn In, char[] Name, ref bool Error)
{
    Texts.Scanner S;
    Texts.Text T;
    Display.Frame F;
    Viewers.Viewer V;
    long Beg;
    long End;
    long Time;
    Error = false;
    In = null;
    if (Name == "*")
    {
        T = TextDocs.GetText(F);
        if (T != null)
        {
            NEW(In);
            Texts.OpenReader(In.R, T, 0);
        }
        else
        {
            Error = true;
        }
    }
    else if (Name == "@")
    {
        Oberon.GetSelection(T, Beg, End, Time);
        if (Time >= 0)
        {
            NEW(In);
            Texts.OpenReader(In.R, T, Beg);
        }
        else
        {
            Error = true;
        }
    }
    else
    {
        if (Name == "^")
        {
            Oberon.GetSelection(T, Beg, End, Time);
            if (Time >= 0)
            {
                Texts.OpenScanner(S, T, Beg);
                Texts.Scan(S);
                COPY(S.s, Name);
            }
            else
            {
                Error = true;
                return;
            }
        }
        T = TextFrames.Text(Name);
        if (T.len != 0)
        {
            NEW(In);
            Texts.OpenReader(In.R, T, 0);
        }
        else
        {
            Error = true;
        }
    }
}

void CloseIn(ref TextIn In)
{
    In = null;
}

void Read(TextIn In, ref char c)
{
    Texts.Read(In.R, c);
}

void Pos(TextIn In, ref Position Pos)
{
    Pos.Offset = Texts.Pos(In.R);
}

void PrevPos(TextIn In, ref Position Pos)
{
    Pos.Offset = Texts.Pos(In.R) - 1;
}

void CreateOut(ref TextOut Out, char[] Name)
{
    NEW(Out);
    Out.Txt = TextFrames.Text("");
    Texts.OpenWriter(Out.W);
    COPY(Name, Out.Name);
    if (Out.Name == "")
    {
        COPY("IOOutStd.Txt", Out.Name);
    }
    Out.IsShown = false;
}

void CreateModOut(ref TextOut Out, char[] Name)
{
    int i;
    NEW(Out);
    Out.Txt = TextFrames.Text("");
    Texts.OpenWriter(Out.W);
    COPY(Name, Out.Name);
    if (Out.Name == "" || Out.Name[0] == ".")
    {
        COPY("IOModStd", Out.Name);
    }
    i = 0;
    while (Out.Name[i] != '\x00' && Out.Name[i] != "." && i < Out.Name.length - 5)
    {
        ++i;
    }
    Out.Name[i] = ".";
    Out.Name[i + 1] = "M";
    Out.Name[i + 2] = "o";
    Out.Name[i + 3] = "d";
    Out.Name[i + 4] = '\x00';
    Out.IsShown = false;
}

void Update(TextOut Out)
{
    Texts.Append(Out.Txt, Out.W.buf);
}

void CloseOut(ref TextOut Out)
{
    Update(Out);
    Out = null;
}

void Show(TextOut Out)
{
    TextFrames.Frame menuF;
    TextFrames.Frame mainF;
    MenuViewers.Viewer V;
    int X;
    int Y;
    Update(Out);
    if (!Out.IsShown)
    {
        mainF = TextFrames.NewText(Out.Txt, 0);
        menuF = TextFrames.NewMenu(Out.Name,
                "System.Close  System.Copy  System.Grow  Edit.Search  Edit.Locate  Edit.Store ");
        Oberon.AllocateUserViewer(Oberon.Mouse.X, X, Y);
        V = MenuViewers.New(menuF, mainF, TextFrames.menuH, X, Y);
        Out.IsShown = true;
    }
}

void WriteText(TextOut Out, char[] Str)
{
    int i;
    char c;
    i = 0;
    c = Str[0];
    while (c != '\x00')
    {
        if (c == "\\")
        {
            ++i;
            c = Str[i];
            switch (c)
            {
            case '\x00':
                return;
                break;
            case "'":
                Texts.Write(Out.W, '\x22');
                break;
            case "t":
                Texts.Write(Out.W, '\x09');
                break;
            case "n":
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
}

void WriteString(TextOut Out, char[] Str)
{
    Texts.WriteString(Out.W, Str);
}

void Write(TextOut Out, char c)
{
    Texts.Write(Out.W, c);
}

void WriteInt(TextOut Out, long i)
{
    Texts.WriteInt(Out.W, i, 0);
}

void WriteIntF(TextOut Out, long i, int Len)
{
    Texts.WriteInt(Out.W, i, Len);
}

void WritePos(TextOut Out, Position Pos)
{
    Texts.WriteString(Out.W, "pos ");
    Texts.WriteInt(Out.W, Pos.Offset, 6);
}

void WriteLn(TextOut Out)
{
    Texts.Write(Out.W, eol);
}

void Compile(TextOut Out, ref bool Error)
{
    Texts.Reader R;
    char[512] Opts;
    Update(Out);
    Texts.OpenReader(R, Out.Txt, 0);
    StringOption(Opts);
    if (Opts[0] == '\x00')
    {
        Opts = standardCompileOpts;
    }
    Compiler.Module(R, Opts, 0, Msg.Txt, Error);
}

void OpenFile(ref File F, char[] Name, ref bool Error)
{
    Files.File File;
    File = Files.Old(Name);
    if (File != null)
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
}

void CreateFile(ref File F, char[] Name)
{
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
}

void CloseFile(ref File F)
{
    Files.Close(Files.Base(F.Rider));
    if (F.NewFile)
    {
        Files.Register(Files.Base(F.Rider));
    }
    F = null;
}

void GetLInt(File F, ref long i)
{
    Files.ReadLInt(F.Rider, i);
}

void GetSet(File F, ref uint s)
{
    Files.ReadSet(F.Rider, s);
}

void PutLInt(File F, long i)
{
    Files.WriteLInt(F.Rider, i);
}

void PutSet(File F, uint s)
{
    Files.WriteSet(F.Rider, s);
}

long TimeStamp()
{
    return Oberon.Time();
}

void NextParam(ref char[] String)
{
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
}

void FirstParam(ref char[] String)
{
    Texts.OpenReader(ParamReader, Oberon.Par.text, Oberon.Par.pos);
    Texts.Read(ParamReader, ParamCh);
    NextParam(String);
}

bool IsOption(char c1)
{
    char[512] String;
    int i;
    char c;
    if (c1 < "a" || "z" < c1)
    {
        return false;
    }
    FirstParam(String);
    while (String[0] == optCh1 || String[0] == optCh2)
    {
        i = 1;
        c = String[1];
        while ("A" <= c && c <= "Z" || "a" <= c && c <= "z")
        {
            if (c == c1 && (String[i + 1] < "A" || "Z" < String[i + 1]))
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

bool IsLongOption(char c1, char c2)
{
    char[512] String;
    int i;
    char c;
    if (c1 < "a" || "z" < c1)
    {
        return false;
    }
    else if (c2 < "A" || "Z" < c2)
    {
        return false;
    }
    FirstParam(String);
    while (String[0] == optCh1 || String[0] == optCh2)
    {
        i = 1;
        c = String[1];
        while ("A" <= c && c <= "Z" || "a" <= c && c <= "z")
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
    char[512] String;
    int i;
    int d;
    char c;
    Num = 0;
    FirstParam(String);
    while (String[0] == optCh1 || String[0] == optCh2)
    {
        i = 1;
        c = String[1];
        if ("0" <= c && c <= "9")
        {
            do
            {
                d = ORD(c) - ORD("0");
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
            while (!(c < "0" || "9" < c));
            return;
        }
        NextParam(String);
    }
}

void StringOption(ref char[] Str)
{
    char[512] String;
    int i;
    char c;
    Str[0] = '\x00';
    FirstParam(String);
    while (String[0] == optCh1 || String[0] == optCh2)
    {
        if (String[1] == "\"")
        {
            i = 2;
            c = String[2];
            while (c != "\"" && c != '\x00' && i < Str.length + 1)
            {
                Str[i - 2] = c;
                ++i;
                c = String[i];
            }
            if (c == "\"")
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

void InputName(ref char[] Name)
{
    FirstParam(Name);
    while (Name[0] == optCh1 || Name[0] == optCh2)
    {
        NextParam(Name);
    }
}

static this()
{
    NEW(Msg);
    Msg.Txt = Oberon.Log;
    Texts.OpenWriter(Msg.W);
    COPY("System.Log", Msg.Name);
    Msg.IsShown = true;
    UndefPos.Offset = -1;
}

module eScanner;

import runtime;
import IO = eIO;
import io : Position, TextIn;
import std.conv : to;
import std.stdio;

const nil = 0;
const firstChar = 0;
const firstIdent = 1;
const errorIdent = firstIdent;
const eot = 0;
const str = '"';
const num = '0';
const ide = 'A';
alias OpenCharBuf = char[];

struct IdentRecord
{
    int Repr;
    int HashNext;
}

alias OpenIdent = IdentRecord[];
int Val;
Position Pos;
OpenCharBuf CharBuf;
int NextChar;
OpenIdent Ident;
int NextIdent;
int[97] HashTable;
TextIn In;
int ErrorCounter;
bool verbose;

void Error(string String)
{
    writeln;
    writeln(IO.Msg, Pos);
    IO.WriteText(IO.Msg, "  ");
    IO.WriteText(IO.Msg, String);
    IO.Update(IO.Msg);
    ++ErrorCounter;
}

void Expand()
{
    if (NextChar >= CharBuf.length)
    {
        OpenCharBuf CharBuf1;

        if (CharBuf.length <= DIV(int.max, 2))
        {
            CharBuf1 = new char[CharBuf.length * 2];
        }
        else
        {
            throw new Exception("internal error: CharBuf overflow");
        }
        for (size_t i = firstChar; i < CharBuf.length; ++i)
        {
            CharBuf1[i] = CharBuf[i];
        }
        CharBuf = CharBuf1;
    }
    if (NextIdent >= Ident.length)
    {
        OpenIdent Ident1;

        if (Ident.length <= DIV(int.max, 2))
        {
            Ident1 = new IdentRecord[Ident.length * 2];
        }
        else
        {
            throw new Exception("internal error: Ident overflow");
        }
        for (size_t i = firstIdent; i < Ident.length; ++i)
        {
            Ident1[i] = Ident[i];
        }
        Ident = Ident1;
    }
}

void Init(TextIn Input)
{
    CharBuf[firstChar] = str;
    CharBuf[firstChar + 1] = 'e';
    CharBuf[firstChar + 2] = 'r';
    CharBuf[firstChar + 3] = 'r';
    NextChar = firstChar + 4;
    Ident[errorIdent].Repr = firstChar;
    Ident[errorIdent + 1].Repr = NextChar;
    NextIdent = firstIdent + 1;
    for (size_t i = 0; i < HashTable.length; ++i)
    {
        HashTable[i] = nil;
    }
    In = Input;
    ErrorCounter = 0;
}

public string toString(int Id)
{
    import std.string : fromStringz;

    char[] Name = new char[256];

    GetRepr(Id, Name);
    return fromStringz(Name.ptr).idup;
}

void GetRepr(int Id, ref char[] Name)
{
    int k;
    int m;
    int n;
    char c;
    k = Ident[Id].Repr;
    c = CharBuf[k];
    n = Ident[Id + 1].Repr - k;
    if (Name.length < n + 1 || Name.length < n + 2 && (c == str || c == '\''))
    {
        throw new Exception("internal error: symbol too long");
    }
    for (m = 0; m <= n - 1; ++m)
    {
        Name[m] = CharBuf[k + m];
    }
    if (c == str || c == '\'')
    {
        Name[n] = c;
        ++n;
    }
    Name[n] = 0;
}

void WriteRepr(IO.TextOut Out, int Id)
{
    int k;
    int m;
    char c;
    k = Ident[Id].Repr;
    c = CharBuf[k];
    for (m = k; m <= Ident[Id + 1].Repr - 1; ++m)
    {
        IO.Write(Out, CharBuf[m]);
    }
    if (c == str || c == '\'')
    {
        IO.Write(Out, c);
    }
}

void Get(ref char Tok)
{
    /**
     * a "!" starts a one line comment inside this comment
     */
    void Comment()
    {
        int Lev = 1;
        dchar c;
        dchar c1;

        while (true)
        {
            c1 = c;
            In.popFront;
            c = In.front;
            if (c1 == '(' && c == '*')
            {
                In.popFront;
                c = In.front;
                ++Lev;
            }
            else if (c1 == '*' && c == ')')
            {
                In.popFront;
                c = In.front;
                --Lev;
                if (Lev == 0)
                {
                    break;
                }
            }
            if (c == '!')
            {
                do
                {
                    In.popFront;
                }
                while (In.front != IO.eol && In.front != eot);
            }
            if (c == eot)
            {
                Error("open comment at end of text");
                break;
            }
        }
    }

    void LookUp(int OldNextChar)
    {
        int Len;
        int First;
        int Last;
        int HashIndex;
        int m;
        int n;

        if (Tok == str)
        {
            First = CharBuf[OldNextChar + 1];
            Len = NextChar - OldNextChar + 1;
        }
        else
        {
            First = CharBuf[OldNextChar];
            Len = NextChar - OldNextChar;
        }
        Last = CharBuf[NextChar - 1];
        HashIndex = cast(int) MOD(((First + Last) * 2 - Len) * 4 - First, HashTable.length);
        Val = HashTable[HashIndex];
        while (Val != nil)
        {
            n = OldNextChar;
            m = Ident[Val].Repr;
            if (Tok == str && (CharBuf[m] == str || CharBuf[m] == '\''))
            {
                ++n;
                ++m;
            }
            while (CharBuf[n] == CharBuf[m])
            {
                ++n;
                ++m;
            }
            if (n == NextChar && m == Ident[Val + 1].Repr)
            {
                NextChar = OldNextChar;
                return;
            }
            else
            {
                Val = Ident[Val].HashNext;
            }
        }
        Val = NextIdent;
        Ident[Val].Repr = OldNextChar;
        Ident[Val].HashNext = HashTable[HashIndex];
        HashTable[HashIndex] = Val;
        ++NextIdent;
        if (NextIdent == Ident.length)
        {
            Expand;
        }
        Ident[NextIdent].Repr = NextChar;
    }

    void String()
    {
        const Terminator = In.front;
        const OldNextChar = NextChar;
        dchar c = str;

        do
        {
            if (NextChar == CharBuf.length)
                Expand;
            CharBuf[NextChar] = c.to!char;
            ++NextChar;
            In.popFront;
            c = In.front;
            if (c == IO.eol || c == eot)
            {
                Error("string terminator not in this line");
                NextChar = OldNextChar;
                Val = errorIdent;
                return;
            }
            else if (c < ' ')
            {
                Error("illegal character in string");
                NextChar = OldNextChar;
                Val = errorIdent;
                do
                    In.popFront;
                while (In.front != Terminator && In.front != IO.eol && In.front != eot);
                if (In.front == Terminator)
                    In.popFront;
                return;
            }
            else if (c == str && Terminator != str)
            {
                CharBuf[NextChar] = '\\';
                ++NextChar;
                if (NextChar == CharBuf.length)
                    Expand;
            }
        }
        while (c != Terminator);
        In.popFront;
        if (NextChar == OldNextChar + 1)
        {
            Error("illegal empty string");
            NextChar = OldNextChar;
            Val = errorIdent;
            return;
        }
        if (NextChar == CharBuf.length)
            Expand;
        CharBuf[NextChar] = IO.eol;
        LookUp(OldNextChar);
    }

    void Ident()
    {
        const OldNextChar = NextChar;

        do
        {
            if (NextChar == CharBuf.length)
            {
                Expand;
            }
            CharBuf[NextChar] = In.front.to!char;
            ++NextChar;
            In.popFront;
        }
        while ('A' <= In.front && In.front <= 'Z' || 'a' <= In.front && In.front <= 'z');
        if (NextChar == CharBuf.length)
        {
            Expand;
        }
        CharBuf[NextChar] = IO.eol;
        LookUp(OldNextChar);
    }

    void Number()
    {
        bool Ok = true;

        Val = 0;
        do
        {
            if (Ok)
            {
                const d = In.front - '0';

                if (Val <= 999)
                {
                    Val = Val * 10 + d;
                }
                else
                {
                    Error("number out of range 0 ... 9999");
                    Ok = false;
                    Val = 0;
                }
            }
            In.popFront;
        }
        while ('0' <= In.front && In.front <= '9');
    }

    while (true)
    {
        while (In.front <= ' ' && In.front != eot)
        {
            In.popFront;
        }
        if (In.front == '!')
        {
            do
            {
                In.popFront;
            }
            while (In.front != IO.eol && In.front != eot);
        }
        else if (In.front == '(')
        {
            Pos = In.position;
            In.popFront;
            if (In.front == '*')
            {
                Comment;
            }
            else
            {
                Tok = '(';
                return;
            }
        }
        else
        {
            break;
        }
    }
    Pos = In.position;
    if (In.front == str || In.front == '\'')
    {
        Tok = str;
        String;
    }
    else if ('A' <= In.front && In.front <= 'Z' || 'a' <= In.front && In.front <= 'z')
    {
        Tok = ide;
        Ident;
    }
    else if ('0' <= In.front && In.front <= '9')
    {
        Tok = num;
        Number;
    }
    else if (In.front == '~' || In.front == eot)
    {
        Tok = eot;
    }
    else
    {
        Tok = In.front.to!char;
        In.popFront;
    }
    if (IO.IsOption('v'))
        trace(Tok);
}

void trace(char tok)
{
    import std.stdio : write, writef, writeln;

    write(Pos, ' ');
    if (tok == ide || tok == str)
    {
        write((tok == ide) ? "ide" : "str");
        writef!"[%s] = "(Val);
        WriteRepr(IO.Msg, Val);
        IO.Update(IO.Msg);
        writeln;
    }
    else if (tok == num)
        writeln("num = ", Val);
    else
        writeln(tok);
}

static this()
{
    CharBuf = new char[1023];
    Ident = new IdentRecord[255];
}

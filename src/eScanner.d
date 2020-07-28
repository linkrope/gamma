module eScanner;

import runtime;
import IO = eIO;

const nil = 0;
const firstChar = 0;
const firstIdent = 1;
const errorIdent = firstIdent;
const eot = '\x00';
const str = '"';
const num = '0';
const ide = 'A';
alias OpenCharBuf = char[];

class IdentRecord
{
    int Repr;
    int HashNext;
}

alias OpenIdent = IdentRecord[];
int Val;
IO.Position Pos;
char c;
OpenCharBuf CharBuf;
int NextChar;
OpenIdent Ident;
int NextIdent;
int[97] HashTable;
IO.TextIn In;
int ErrorCounter;
bool verbose;

void Error(string String)
{
    IO.WriteText(IO.Msg, "\n  ");
    IO.WritePos(IO.Msg, Pos);
    IO.WriteText(IO.Msg, "  ");
    IO.WriteText(IO.Msg, String);
    IO.Update(IO.Msg);
    ++ErrorCounter;
}

void Expand()
{
    long i;
    OpenCharBuf CharBuf1;
    OpenIdent Ident1;
    if (NextChar >= CharBuf.length)
    {
        if (CharBuf.length <= DIV(int.max, 2))
        {
            NEW(CharBuf1, CharBuf.length * 2);
        }
        else
        {
            throw new Exception("internal error: CharBuf overflow");
        }
        for (i = firstChar; i <= CharBuf.length - 1; ++i)
        {
            CharBuf1[i] = CharBuf[i];
        }
        CharBuf = CharBuf1;
    }
    if (NextIdent >= Ident.length)
    {
        if (Ident.length <= DIV(int.max, 2))
        {
            NEW(Ident1, Ident.length * 2);
        }
        else
        {
            throw new Exception("internal error: Ident overflow");
        }
        for (i = firstIdent; i <= Ident.length - 1; ++i)
        {
            Ident1[i] = Ident[i];
        }
        Ident = Ident1;
    }
}

void Init(IO.TextIn Input)
{
    int i;
    c = ' ';
    CharBuf[firstChar] = str;
    CharBuf[firstChar + 1] = 'e';
    CharBuf[firstChar + 2] = 'r';
    CharBuf[firstChar + 3] = 'r';
    NextChar = firstChar + 4;
    Ident[errorIdent].Repr = firstChar;
    Ident[errorIdent + 1].Repr = NextChar;
    NextIdent = firstIdent + 1;
    for (i = 0; i <= HashTable.length - 1; ++i)
    {
        HashTable[i] = nil;
    }
    In = Input;
    ErrorCounter = 0;
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
    Name[n] = '\x00';
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
        int Lev;
        char c1;
        Lev = 1;
        c = ' ';
        while (true)
        {
            c1 = c;
            IO.Read(In, c);
            if (c1 == '(' && c == '*')
            {
                IO.Read(In, c);
                ++Lev;
            }
            else if (c1 == '*' && c == ')')
            {
                IO.Read(In, c);
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
                    IO.Read(In, c);
                }
                while (!(c == IO.eol || c == eot));
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
            First = ORD(CharBuf[OldNextChar + 1]);
            Len = NextChar - OldNextChar + 1;
        }
        else
        {
            First = ORD(CharBuf[OldNextChar]);
            Len = NextChar - OldNextChar;
        }
        Last = ORD(CharBuf[NextChar - 1]);
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
        char Terminator;
        int OldNextChar;
        OldNextChar = NextChar;
        Terminator = c;
        do
        {
            if (NextChar == CharBuf.length)
            {
                Expand;
            }
            CharBuf[NextChar] = c;
            ++NextChar;
            IO.Read(In, c);
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
                {
                    IO.Read(In, c);
                }
                while (!(c == Terminator || c == IO.eol || c == eot));
                if (c == Terminator)
                {
                    IO.Read(In, c);
                }
                return;
            }
        }
        while (!(c == Terminator));
        IO.Read(In, c);
        if (NextChar == OldNextChar + 1)
        {
            Error("illegal empty string");
            NextChar = OldNextChar;
            Val = errorIdent;
            return;
        }
        if (NextChar == CharBuf.length)
        {
            Expand;
        }
        CharBuf[NextChar] = IO.eol;
        LookUp(OldNextChar);
    }

    void Ident()
    {
        int OldNextChar;
        OldNextChar = NextChar;
        do
        {
            if (NextChar == CharBuf.length)
            {
                Expand;
            }
            CharBuf[NextChar] = c;
            ++NextChar;
            IO.Read(In, c);
        }
        while ('A' <= c && c <= 'Z' || 'a' <= c && c <= 'z');
        if (NextChar == CharBuf.length)
        {
            Expand;
        }
        CharBuf[NextChar] = IO.eol;
        LookUp(OldNextChar);
    }

    void Number()
    {
        int d;
        bool Ok;
        Val = 0;
        Ok = true;
        do
        {
            if (Ok)
            {
                d = ORD(c) - ORD('0');
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
            IO.Read(In, c);
        }
        while ('0' <= c && c <= '9');
    }

    while (true)
    {
        while (c <= ' ' && c != eot)
        {
            IO.Read(In, c);
        }
        if (c == '!')
        {
            do
            {
                IO.Read(In, c);
            }
            while (c != IO.eol && c != eot);
        }
        else if (c == '(')
        {
            IO.PrevPos(In, Pos);
            IO.Read(In, c);
            if (c == '*')
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
    IO.PrevPos(In, Pos);
    if (c == str || c == '\'')
    {
        Tok = str;
        String;
    }
    else if ('A' <= c && c <= 'Z' || 'a' <= c && c <= 'z')
    {
        Tok = ide;
        Ident;
    }
    else if ('0' <= c && c <= '9')
    {
        Tok = num;
        Number;
    }
    else if (c == '~' || c == eot)
    {
        Tok = eot;
    }
    else
    {
        Tok = c;
        IO.Read(In, c);
    }
    if (verbose)
        trace(Tok);
}

void trace(char tok)
{
    import std.stdio : write, writef, writeln;

    writef!"%6d: "(Pos.Offset);
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
    NEW(CharBuf, 1023);
    NEW(Ident, 255);
    foreach (ref ident; Ident)
        ident = new IdentRecord;
}

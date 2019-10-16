module eSplit;
import runtime;
import IO = eIO;
import Sets = eSets;

const maxDataLinks = 64;
const maxLinks = 256;
const setLen = 5000;
const procMods = 2;
const baseMods = 1;
const nil = -1;
const eof = -2;
const number = -3;
const ident = -4;
const string = -5;
const comment = -6;
const plus = -10;
const minus = -11;
const equal = -13;
const unequal = -14;
const less = -15;
const lesseq = -16;
const greater = -17;
const greatereq = -18;
const not = -19;
const and = -20;
const left = -21;
const right = -22;
const arrow = -23;
const period = -24;
const comma = -25;
const colon = -26;
const semicolon = -27;
const slash = -28;
const star = -29;
const lbrak = -30;
const rbrak = -31;
const lbrace = -32;
const rbrace = -33;
const is_ = -34;
const bar = -35;
const initialBufLen = 1000;
const initialReprLen = 200;
alias OpenBuf = char[];
alias OpenRepr = long[];
OpenBuf Buf;
OpenRepr Repr;
long NextCh;
long NextId;
long Tok;
long Val;
IO.Position Pos;
char c;
IO.TextIn In;
void Error(char[] s)
{
    long r;
    long c;
    IO.WritePos(IO.Msg, Pos);
    IO.WriteString(IO.Msg, ": ");
    IO.WriteString(IO.Msg, s);
    IO.WriteLn(IO.Msg);
    IO.Update(IO.Msg);
    HALT(99);
}

void Str(char[] s)
{
    IO.WriteText(IO.Msg, s);
    IO.Update(IO.Msg);
}

void Expand()
{
    OpenBuf Buf1;
    OpenRepr Repr1;
    long i;
    if (NextId >= Repr.length - 1)
    {
        NEW(Repr1, 2 * Repr.length);
        for (i = 0; i <= Repr.length - 1; ++i)
        {
            Repr1[i] = Repr[i];
        }
        Repr = Repr1;
    }
    if (NextCh >= Buf.length - 1)
    {
        NEW(Buf1, 2 * Buf.length);
        for (i = 0; i <= Buf.length - 1; ++i)
        {
            Buf1[i] = Buf[i];
        }
        Buf = Buf1;
    }
}

long Enter(char[] s)
{
    long n;
    char c;
    if (NextId > Repr.length - 1)
    {
        Expand;
    }
    Repr[NextId] = NextCh;
    ++NextId;
    n = 0;
    do
    {
        if (NextCh > Buf.length - 1)
        {
            Expand;
        }
        c = s[n];
        Buf[NextCh] = c;
        ++n;
        ++NextCh;
    }
    while (!(c == '\x00'));
    return NextId - 1;
}

void WriteRepr(IO.TextOut Out, long Id)
{
    long n;
    n = Repr[Id];
    do
    {
        IO.Write(Out, Buf[n]);
        ++n;
    }
    while (!(Buf[n] == '\x00'));
}

void GetRepr(ref char[] Out, long Id)
{
    long n;
    long m;
    n = Repr[Id] - 1;
    m = 0;
    do
    {
        ++n;
        Out[m] = Buf[n];
        ++m;
    }
    while (!(Buf[n] == '\x00'));
}

void WriteToken(IO.TextOut Out, long Tok)
{
    switch (Tok)
    {
    case plus:
        IO.Write(Out, "+");
        break;
    case minus:
        IO.Write(Out, "-");
        break;
    case equal:
        IO.Write(Out, "=");
        break;
    case unequal:
        IO.Write(Out, "#");
        break;
    case less:
        IO.Write(Out, "<");
        break;
    case lesseq:
        IO.WriteString(Out, "<=");
        break;
    case greater:
        IO.Write(Out, ">");
        break;
    case greatereq:
        IO.WriteString(Out, ">=");
        break;
    case not:
        IO.Write(Out, "~");
        break;
    case and:
        IO.Write(Out, "&");
        break;
    case left:
        IO.Write(Out, "(");
        break;
    case right:
        IO.Write(Out, ")");
        break;
    case arrow:
        IO.Write(Out, "^");
        break;
    case period:
        IO.Write(Out, ".");
        break;
    case comma:
        IO.Write(Out, ",");
        break;
    case colon:
        IO.Write(Out, ":");
        break;
    case semicolon:
        IO.Write(Out, ";");
        break;
    case slash:
        IO.Write(Out, "/");
        break;
    case star:
        IO.Write(Out, "*");
        break;
    case lbrak:
        IO.Write(Out, "[");
        break;
    case rbrak:
        IO.Write(Out, "]");
        break;
    case lbrace:
        IO.Write(Out, "{");
        break;
    case rbrace:
        IO.Write(Out, "}");
        break;
    case is_:
        IO.WriteString(Out, ":=");
        break;
    case bar:
        IO.Write(Out, "|");
        break;
    default:
        IO.Write(Out, c);
    }
}

void Get()
{
    const EOT = '\x00';
    const EOL = '\x0d';
    const STR = '\x22';
    bool Ziffer(char c)
    {
        if (c >= "0" && c <= "9")
        {
            return true;
        }
        return false;
    }

    bool Buchstabe(char c)
    {
        if (c >= "A" && c <= "Z" || c >= "a" && c <= "z")
        {
            return true;
        }
        return false;
    }

    void AddString(long NextCh1)
    {
        long Id;
        long n;
        long m;
        Buf[NextCh] = EOL;
        Id = 0;
        while (Id < NextId)
        {
            n = NextCh1;
            m = Repr[Id];
            while (Buf[n] == Buf[m])
            {
                ++n;
                ++m;
            }
            if (n == NextCh && Buf[m] == '\x00')
            {
                NextCh = NextCh1;
                Val = Id;
                return;
            }
            else
            {
                ++Id;
            }
        }
        if (NextId >= Repr.length - 1)
        {
            Expand;
        }
        if (NextCh >= Buf.length - 1)
        {
            Expand;
        }
        Buf[NextCh] = '\x00';
        ++NextCh;
        Repr[NextId] = NextCh1;
        ++NextId;
        Val = Id;
    }

    void Number()
    {
        long d;
        Val = 0;
        do
        {
            d = ORD(c) - ORD("0");
            if (Val <= DIV(long.max - d, 10))
            {
                Val = Val * 10 + d;
                IO.Read(In, c);
            }
            else
            {
                Error("number > MAX(LONGINT)");
            }
        }
        while (!!Ziffer(c));
        Tok = number;
    }

    void Identifier()
    {
        long Id;
        long NextCh1;
        long n;
        long m;
        NextCh1 = NextCh;
        do
        {
            if (NextCh >= Buf.length - 1)
            {
                Expand;
            }
            Buf[NextCh] = c;
            ++NextCh;
            IO.Read(In, c);
        }
        while (!(!Buchstabe(c) && !Ziffer(c)));
        AddString(NextCh1);
    }

    void String()
    {
        long NextCh1;
        char c1;
        c1 = c;
        NextCh1 = NextCh;
        do
        {
            if (NextCh >= Buf.length - 1)
            {
                Expand;
            }
            Buf[NextCh] = c;
            ++NextCh;
            IO.Read(In, c);
        }
        while (!(c == c1 || c == EOL || c == EOT));
        if (c != c1)
        {
            Error("string not closed");
            return;
        }
        if (NextCh >= Buf.length - 1)
        {
            Expand;
        }
        Buf[NextCh] = c;
        ++NextCh;
        IO.Read(In, c);
        AddString(NextCh1);
    }

    void Comment()
    {
        long Level;
        IO.Read(In, c);
        Level = 1;
        while (true)
        {
            if (c == EOT)
            {
                Error("comment not closed");
                break;
            }
            else if (c == "(")
            {
                IO.Read(In, c);
                if (c == "*")
                {
                    IO.Read(In, c);
                    ++Level;
                }
            }
            else if (c == "*")
            {
                IO.Read(In, c);
                if (c == ")")
                {
                    IO.Read(In, c);
                    --Level;
                    if (Level == 0)
                    {
                        break;
                    }
                }
            }
            else
            {
                IO.Read(In, c);
            }
        }
    }

    while (c <= " ")
    {
        if (c != '\x00')
        {
            IO.Read(In, c);
        }
        else
        {
            Tok = eof;
            return;
        }
    }
    IO.PrevPos(In, Pos);
    switch (c)
    {
    case "a": .. case "z":
    case "A": .. case "Z":
        Identifier;
        Tok = ident;
        break;
    case "!":
        do
        {
            IO.Read(In, c);
        }
        while (!(c == EOL));
        Get;
        break;
    case "(":
        IO.Read(In, c);
        if (c == "*")
        {
            Comment;
            Get;
        }
        else
        {
            Tok = left;
        }
        break;
    case ")":
        IO.Read(In, c);
        Tok = right;
        break;
    case "-":
        IO.Read(In, c);
        Tok = minus;
        break;
    case "*":
        IO.Read(In, c);
        Tok = star;
        break;
    case ",":
        IO.Read(In, c);
        Tok = comma;
        break;
    case "0": .. case "9":
        Number;
        break;
    case "+":
        IO.Read(In, c);
        Tok = plus;
        break;
    case "/":
        IO.Read(In, c);
        Tok = slash;
        break;
    case "=":
        IO.Read(In, c);
        Tok = equal;
        break;
    case "#":
        IO.Read(In, c);
        Tok = unequal;
        break;
    case "&":
        IO.Read(In, c);
        Tok = and;
        break;
    case "<":
        IO.Read(In, c);
        if (c == ">")
        {
            Tok = unequal;
            IO.Read(In, c);
        }
        else if (c == "=")
        {
            Tok = lesseq;
            IO.Read(In, c);
        }
        else
        {
            Tok = less;
        }
        break;
    case ">":
        IO.Read(In, c);
        if (c == "=")
        {
            Tok = greatereq;
            IO.Read(In, c);
        }
        else
        {
            Tok = greater;
        }
        break;
    case ":":
        IO.Read(In, c);
        if (c == "=")
        {
            IO.Read(In, c);
            Tok = is_;
        }
        else
        {
            Tok = colon;
        }
        break;
    case ";":
        IO.Read(In, c);
        Tok = semicolon;
        break;
    case ".":
        IO.Read(In, c);
        Tok = period;
        break;
    case "^":
        IO.Read(In, c);
        Tok = arrow;
        break;
    case "'":
    case STR:
        String;
        Tok = string;
        break;
    case "[":
        IO.Read(In, c);
        Tok = lbrak;
        break;
    case "]":
        IO.Read(In, c);
        Tok = rbrak;
        break;
    case "{":
        IO.Read(In, c);
        Tok = lbrace;
        break;
    case "}":
        IO.Read(In, c);
        Tok = rbrace;
        break;
    case "~":
        IO.Read(In, c);
        Tok = not;
        break;
    case "|":
        IO.Read(In, c);
        Tok = bar;
        break;
    default:
        IO.Read(In, c);
        Tok = nil;
        Error("character not allowed");
    }
}

void ScannerInit()
{
    char[512] Name;
    bool OpenError;
    IO.InputName(Name);
    IO.OpenIn(In, Name, OpenError);
    if (OpenError)
    {
        Str("\nfatal error: cannot open input\n");
        HALT(99);
    }
    NextCh = 0;
    NextId = 0;
    NEW(Buf, initialBufLen);
    NEW(Repr, initialReprLen);
    c = " ";
}

void Split()
{
    const firstProc = 1;
    const top = 0;
    const bottom = 0;
    class ProcRecord
    {
        long Name;
        long Mod;
    }

    alias OpenProc = ProcRecord[];
    alias OpenInt = long[];
    IO.TextOut[] Mod;
    IO.TextOut[] BMod;
    long CurBase;
    long ModuleName;
    long Keywords;
    long i;
    Sets.OpenSet Exported;
    OpenInt BaseModule;
    OpenProc Proc;
    long NextProc;
    bool ShowCode;
    long Module;
    long Procedure;
    long Import;
    long Var;
    long Type;
    long Const;
    long End;
    long IOMod;
    long SMod;
    long EvalMod;
    void Expand()
    {
        OpenProc Proc1;
        OpenInt BM;
        long i;
        if (NextProc >= Proc.length - 1)
        {
            NEW(Proc1, 2 * Proc.length);
            for (i = 0; i <= Proc.length - 1; ++i)
            {
                Proc1[i] = Proc[i];
            }
            Proc = Proc1;
        }
        else if (Repr.length > BaseModule.length)
        {
            NEW(BM, Repr.length);
            for (i = 0; i <= BaseModule.length - 1; ++i)
            {
                BM[i] = BaseModule[i];
            }
            for (i = BaseModule.length; i <= BM.length - 1; ++i)
            {
                BM[i] = -1;
            }
            BaseModule = BM;
        }
    }

    void Insert(long Name, long Module)
    {
        ASSERT(Module >= 0, 95);
        if (Name >= BaseModule.length)
        {
            Expand;
        }
        ASSERT(BaseModule[Name] < 0, 96);
        BaseModule[Name] = Module;
    }

    long BaseInd(long Name)
    {
        ASSERT(Name >= 0, 95);
        if (Name >= BaseModule.length)
        {
            Expand;
        }
        return BaseModule[Name];
    }

    void Append(ref char[] s1, char[] s2)
    {
        int i;
        int j;
        char ch;
        i = 0;
        j = 0;
        while (s1[i] != '\x00')
        {
            ++i;
        }
        do
        {
            ch = s2[j];
            s1[i] = ch;
            ++i;
            ++j;
        }
        while (!(ch == '\x00'));
    }

    void AppendInt(ref char[] s1, long n)
    {
        long i;
        long base;
        if (n == 0)
        {
            return;
        }
        i = 0;
        base = 1000000000;
        while (s1[i] != '\x00')
        {
            ++i;
        }
        while (DIV(n, base) == 0 && base != 1)
        {
            base = DIV(base, 10);
        }
        do
        {
            s1[i] = CHR(DIV(n, base) + ORD("0"));
            ++i;
            n = MOD(n, base);
            base = DIV(base, 10);
        }
        while (!(base == 0));
        s1[i] = '\x00';
    }

    void Emit(IO.TextOut Out, char[] Str)
    {
        IO.WriteText(Out, Str);
    }

    void ModInt(long i, long n)
    {
        IO.WriteInt(Mod[i], n);
    }

    void WriteBaseName(IO.TextOut Out, long Module)
    {
        ASSERT(Module >= 0, 96);
        Emit(Out, "Base");
        if (Module != bottom)
        {
            IO.WriteInt(Out, Module);
        }
    }

    void WriteTok(IO.TextOut Out, long Tok)
    {
        if (Tok == ident || Tok == string)
        {
            WriteRepr(Out, Val);
        }
        else if (Tok == number)
        {
            IO.WriteInt(Out, Val);
        }
        else
        {
            WriteToken(Out, Tok);
        }
        IO.Write(Out, " ");
    }

    void Bases(char[] Str)
    {
        long i;
        for (i = 0; i <= BMod.length - 1; ++i)
        {
            Emit(BMod[i], Str);
        }
    }

    void Broadcast(long T)
    {
        long i;
        for (i = 0; i <= BMod.length - 1; ++i)
        {
            WriteTok(BMod[i], T);
        }
        for (i = 0; i <= Mod.length - 1; ++i)
        {
            WriteTok(Mod[i], T);
        }
    }

    void NextTok(IO.TextOut Out, long T)
    {
        while (Tok != T && Tok != eof)
        {
            WriteTok(Out, Tok);
            Get;
        }
    }

    void ImportDecl()
    {
        Get;
        while (Tok != semicolon && Tok != eof)
        {
            Broadcast(Tok);
            Get;
        }
        Broadcast(semicolon);
        Get;
    }

    void ConstDecl()
    {
        Broadcast(Tok);
        Get;
        while (Tok == ident && Val > Keywords)
        {
            while (Tok != semicolon && Tok != eof)
            {
                Broadcast(Tok);
                Get;
            }
            Broadcast(semicolon);
            Get;
        }
    }

    void VarDecl()
    {
        IO.TextOut Bottom;
        Bottom = BMod[bottom];
        Emit(Bottom, "\nVAR \n");
        Get;
        while (Tok == ident && Val > Keywords)
        {
            while (Tok != colon)
            {
                if (Tok == ident)
                {
                    Insert(Val, CurBase);
                    WriteRepr(Bottom, Val);
                    IO.Write(Bottom, "*");
                }
                else
                {
                    WriteTok(Bottom, Tok);
                }
                Get;
            }
            Emit(Bottom, ": ");
            Get;
            NextTok(Bottom, semicolon);
            Emit(Bottom, "; \n");
            Get;
        }
    }

    void TypeDecl()
    {
        IO.TextOut Bottom;
        long Name;
        long i;
        Bottom = BMod[bottom];
        Bases("\nTYPE \n");
        Get;
        while (Tok == ident && Val > Keywords)
        {
            Name = Val;
            Insert(Name, bottom);
            for (i = 0; i <= BMod.length - 1; ++i)
            {
                WriteRepr(BMod[i], Name);
                if (i != bottom)
                {
                    Emit(BMod[i], " = Base.");
                    WriteRepr(BMod[i], Name);
                }
            }
            Get;
            if (Tok == star)
            {
                Sets.Incl(Exported, SHORT(Name));
                Emit(Mod[top], "\nTYPE \n");
                WriteRepr(Mod[top], Name);
                Emit(Mod[top], "* = Base.");
                WriteRepr(Mod[top], Name);
                Emit(Mod[top], "; \n");
                Get;
            }
            IO.Write(Bottom, "*");
            NextTok(Bottom, semicolon);
            Bases("; \n");
            Get;
        }
    }

    void ProcDecl()
    {
        long ProcName;
        long CurMod;
        bool Export;
        bool Forward;
        bool MakeDecl;
        IO.TextOut BaseMod;
        IO.TextOut ProcMod;
        void WriteIdent(long Name)
        {
            if (BaseInd(Name) >= bottom)
            {
                if (!(CurMod == top && Sets.In(Exported, SHORT(Name))))
                {
                    WriteBaseName(ProcMod, BaseInd(Name));
                    IO.Write(ProcMod, ".");
                }
                WriteTok(ProcMod, Tok);
            }
            else
            {
                WriteTok(ProcMod, Tok);
            }
        }

        void Formal()
        {
            void NextTok()
            {
                if (MakeDecl)
                {
                    WriteTok(BaseMod, Tok);
                }
                if (!Forward)
                {
                    if (Tok == ident)
                    {
                        WriteIdent(Val);
                    }
                    else
                    {
                        WriteTok(ProcMod, Tok);
                    }
                }
                Get;
            }

            if (MakeDecl)
            {
                Emit(BaseMod, "\n VAR ");
                WriteRepr(BaseMod, ProcName);
                Emit(BaseMod, "*: PROCEDURE ");
            }
            if (Tok == left)
            {
                NextTok;
                while (Tok != right && Tok != eof)
                {
                    NextTok;
                }
                NextTok;
                if (Tok == colon)
                {
                    while (Tok != semicolon && Tok != eof)
                    {
                        NextTok;
                    }
                }
            }
            if (MakeDecl)
            {
                Emit(BaseMod, "; ");
            }
            if (!Forward)
            {
                Emit(ProcMod, "; \n");
            }
            Get;
        }

        Export = false;
        Forward = false;
        MakeDecl = false;
        Get;
        if (Tok == arrow)
        {
            Forward = true;
            Get;
        }
        if (Tok == ident)
        {
            ProcName = Val;
        }
        else
        {
            Error("not a procedure name");
        }
        Get;
        if (BaseInd(ProcName) < 0)
        {
            MakeDecl = true;
            CurBase = MOD(CurBase + 1, BMod.length);
            BaseMod = BMod[CurBase];
            Insert(ProcName, CurBase);
        }
        if (Tok == star)
        {
            Export = true;
            CurMod = top;
            Sets.Incl(Exported, SHORT(ProcName));
            Get;
        }
        else
        {
            CurMod = MOD(NextProc, Mod.length);
        }
        if (Forward)
        {
            Formal;
        }
        else
        {
            Proc[NextProc].Name = ProcName;
            ProcMod = Mod[CurMod];
            Proc[NextProc].Mod = CurMod;
            ++NextProc;
            if (NextProc > Proc.length - 1)
            {
                Expand;
            }
            Emit(ProcMod, "\nPROCEDURE ");
            if (!Export)
            {
                Emit(ProcMod, "* ");
            }
            WriteRepr(ProcMod, ProcName);
            if (Export)
            {
                Emit(ProcMod, "* ");
            }
            else
            {
                IO.Write(ProcMod, " ");
            }
            Formal;
            while (true)
            {
                if (Tok == eof)
                {
                    Error("unexpected end of file");
                    break;
                }
                else if (Tok == ident)
                {
                    if (Val == End)
                    {
                        WriteTok(ProcMod, Tok);
                        Get;
                        if (Tok == ident && Val == ProcName)
                        {
                            Get;
                            if (Tok == semicolon)
                            {
                                WriteRepr(ProcMod, ProcName);
                                Emit(ProcMod, "; \n");
                                Get;
                                break;
                            }
                            else
                            {
                                WriteIdent(ProcName);
                            }
                        }
                    }
                    else
                    {
                        WriteIdent(Val);
                        Get;
                    }
                }
                else
                {
                    WriteTok(ProcMod, Tok);
                    Get;
                }
            }
            IO.Update(ProcMod);
        }
    }

    void MainBlock(IO.TextOut Out)
    {
        Emit(Out, "\nPROCEDURE XXXMainXXX;\n");
        while (true)
        {
            if (Tok == ident && Val == ModuleName)
            {
                Get;
                if (Tok == period)
                {
                    Emit(Out, "XXXMainXXX; \n");
                    break;
                }
                else
                {
                    WriteRepr(Out, ModuleName);
                }
            }
            else if (Tok == eof)
            {
                Error("unexpected end of file");
                break;
            }
            else
            {
                if (Tok == ident && BaseInd(Val) >= 0)
                {
                    WriteBaseName(Out, BaseInd(Val));
                    IO.Write(Out, ".");
                }
                WriteTok(Out, Tok);
                Get;
            }
        }
    }

    void GenInitProcs()
    {
        long i;
        long Name;
        long M;
        for (i = Mod.length - 1; i <= 1; i = i + -1)
        {
            Emit(Mod[i], "\nPROCEDURE XXXInitXXX*; \nBEGIN \n");
        }
        Emit(Mod[0], "\nPROCEDURE XXXInitXXX; \nBEGIN \n");
        for (i = firstProc; i <= NextProc - 1; ++i)
        {
            ASSERT(Proc != null, 96);
            ASSERT(Proc.length > i, 94);
            Name = Proc[i].Name;
            M = Proc[i].Mod;
            ASSERT(BaseModule.length >= Name, 93);
            WriteBaseName(Mod[M], BaseInd(Name));
            Emit(Mod[M], ".");
            WriteRepr(Mod[M], Name);
            Emit(Mod[M], " := ");
            WriteRepr(Mod[M], Name);
            Emit(Mod[M], "; \n");
        }
        for (i = 0; i <= Mod.length - 1; ++i)
        {
            if (i != Mod.length - 1)
            {
                WriteRepr(Mod[i], ModuleName);
                ModInt(i, i + 1);
                Emit(Mod[i], ".XXXInitXXX \n");
            }
            Emit(Mod[i], "END XXXInitXXX; \n\n");
            if (i == 0)
            {
                Emit(Mod[0], "BEGIN \n\tXXXInitXXX;\n\tXXXMainXXX \n");
            }
            Emit(Mod[i], "END ");
            WriteRepr(Mod[i], ModuleName);
            if (i != 0)
            {
                ModInt(i, i);
            }
            Emit(Mod[i], ". \n ");
        }
    }

    void OpenMods()
    {
        char[64] wname;
        long i;
        long j;
        void ImportBase(long M, long Base)
        {
            WriteBaseName(Mod[M], Base);
            Emit(Mod[M], " := ");
            WriteRepr(Mod[M], ModuleName);
            WriteBaseName(Mod[M], Base);
            Emit(Mod[M], ", ");
        }

        for (i = 0; i <= BMod.length - 1; ++i)
        {
            GetRepr(wname, ModuleName);
            Append(wname, "Base");
            AppendInt(wname, i);
            Append(wname, ".Mod");
            IO.CreateOut(BMod[i], wname);
            Emit(BMod[i], "MODULE ");
            WriteRepr(BMod[i], ModuleName);
            WriteBaseName(BMod[i], i);
            Emit(BMod[i], "; \n\tIMPORT ");
            if (i != 0)
            {
                Emit(BMod[i], "Base := ");
                WriteRepr(BMod[i], ModuleName);
                Emit(BMod[i], "Base, ");
            }
        }
        for (i = 0; i <= Mod.length - 1; ++i)
        {
            GetRepr(wname, ModuleName);
            AppendInt(wname, i);
            Append(wname, ".Mod");
            IO.CreateOut(Mod[i], wname);
            Emit(Mod[i], "MODULE ");
            WriteRepr(Mod[i], ModuleName);
            if (i > 0)
            {
                ModInt(i, i);
            }
            Emit(Mod[i], "; \n\tIMPORT ");
            for (j = 0; j <= BMod.length - 1; ++j)
            {
                ImportBase(i, j);
            }
            if (i < Mod.length - 1)
            {
                WriteRepr(Mod[i], ModuleName);
                ModInt(i, i + 1);
                Emit(Mod[i], ", ");
            }
        }
    }

    void CloseMods()
    {
        long i;
        bool CompileError;
        char[64] fname;
        void Check(char[] fname)
        {
            const INT = 2 * (int.max + 1);
            const Byte = 2 * (short.max + 1);
            IO.File f;
            long i;
            bool Error;
            void Int(long i)
            {
                IO.WriteInt(IO.Msg, i);
            }

            IO.OpenFile(f, fname, Error);
            if (Error)
            {
                Str(fname);
                Str(" not found");
            }
            else
            {
                IO.GetLInt(f, i);
                if (MOD(MOD(i, INT), Byte) == 248)
                {
                    if (DIV(MOD(i, INT), Byte) == 54)
                    {
                        IO.GetLInt(f, i);
                        IO.GetLInt(f, i);
                        IO.GetLInt(f, i);
                        IO.GetLInt(f, i);
                        if (DIV(i, INT) > maxDataLinks)
                        {
                            Str("Warning: ");
                            Str(fname);
                            Str(" is maybe not loadable! (");
                            Int(DIV(i, INT));
                            Str(" data links) \n");
                        }
                        IO.GetLInt(f, i);
                        if (MOD(i, INT) > maxLinks)
                        {
                            Str("Warning: ");
                            Str(fname);
                            Str(" is maybe not loadable! (");
                            Int(MOD(i, INT));
                            Str(" links)\n");
                        }
                    }
                }
            }
        }

        for (i = 0; i <= BMod.length - 1; ++i)
        {
            Emit(BMod[i], "\nEND ");
            WriteRepr(BMod[i], ModuleName);
            WriteBaseName(BMod[i], i);
            Emit(BMod[i], ".\n\n");
            IO.Update(BMod[i]);
            if (ShowCode)
            {
                IO.Show(BMod[i]);
            }
            else
            {
                IO.Compile(BMod[i], CompileError);
                if (CompileError)
                {
                    IO.Show(BMod[i]);
                }
                else
                {
                    GetRepr(fname, ModuleName);
                    Append(fname, "Base");
                    AppendInt(fname, i);
                    Append(fname, ".Obj");
                    Check(fname);
                }
            }
        }
        i = Mod.length - 1;
        while (true)
        {
            IO.Update(Mod[i]);
            if (ShowCode)
            {
                IO.Show(Mod[i]);
                IO.WriteLn(IO.Msg);
            }
            else
            {
                IO.Compile(Mod[i], CompileError);
                if (CompileError)
                {
                    IO.Show(Mod[i]);
                    break;
                }
                else
                {
                    GetRepr(fname, ModuleName);
                    AppendInt(fname, i);
                    Append(fname, ".Obj");
                    Check(fname);
                }
            }
            if (i == 0)
            {
                break;
            }
            --i;
        }
        if (CompileError)
        {
            Str("\terrors occured \n");
        }
    }

    void Init()
    {
        long Num;
        long BMods;
        long Mods;
        long i;
        ScannerInit;
        Module = Enter("MODULE");
        Procedure = Enter("PROCEDURE");
        Import = Enter("IMPORT");
        Var = Enter("VAR");
        Type = Enter("TYPE");
        Const = Enter("CONST");
        End = Enter("ARRAY");
        End = Enter("BEGIN");
        End = Enter("CASE");
        End = Enter("DIV");
        End = Enter("DO");
        End = Enter("ELSE");
        End = Enter("ELSIF");
        End = Enter("IS");
        End = Enter("LOOP");
        End = Enter("MOD");
        End = Enter("NIL");
        End = Enter("OF");
        End = Enter("OR");
        End = Enter("POINTER");
        End = Enter("TO");
        End = Enter("TYPE");
        End = Enter("UNTIL");
        End = Enter("WHILE");
        End = Enter("END");
        IOMod = Enter("IO");
        SMod = Enter("S");
        EvalMod = Enter("Eval");
        Keywords = EvalMod;
        NEW(BaseModule, initialReprLen);
        for (i = 0; i <= BaseModule.length - 1; ++i)
        {
            BaseModule[i] = -1;
        }
        Sets.New(Exported, setLen);
        NEW(Proc, 50);
        NextProc = firstProc;
        ShowCode = IO.IsOption("m");
        IO.NumOption(Num);
        Mods = MOD(Num, 100);
        BMods = DIV(Num, 100);
        if (Mods < 1)
        {
            Mods = procMods;
        }
        NEW(Mod, Mods);
        if (BMods < 1)
        {
            BMods = baseMods;
        }
        NEW(BMod, BMods);
        CurBase = 0;
    }

    Init;
    Get;
    if (Tok == ident && Val == Module)
    {
        Get;
    }
    else
    {
        Error("no Oberon module");
    }
    if (Tok == ident)
    {
        ModuleName = Val;
        Get;
    }
    else
    {
        WriteTok(IO.Msg, Tok);
        Error("not a module name");
    }
    Get;
    Str("Split splitting\t");
    WriteRepr(IO.Msg, ModuleName);
    Str("\n");
    OpenMods;
    if (Tok == ident && Val == Import)
    {
        ImportDecl;
    }
    while (true)
    {
        if (Tok == ident)
        {
            if (Val == Const)
            {
                ConstDecl;
            }
            else if (Val == Type)
            {
                TypeDecl;
            }
            else if (Val == Var)
            {
                VarDecl;
            }
            else
            {
                break;
            }
        }
        else
        {
            break;
        }
    }
    while (Tok == ident && Val == Procedure)
    {
        ProcDecl;
    }
    MainBlock(Mod[top]);
    GenInitProcs;
    CloseMods;
    Str("Ready. \n");
}

static this()
{
    Str("eSplit  JoDe 11/96 \n");
}

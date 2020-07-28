module $;
import runtime;
import IO = eIO;
import S = $;

const nToks = $;
const tokSetLen = $;
const nSetT = $;
const nSet = $;
const M = 31 + 1;
const endTok = 0;
const sepTok = 2;
const firstRecStack = 1;
alias OpenRecStack = int[];
alias TokSet = uint[tokSetLen];
int Tok;
OpenRecStack RecStack;
int RecTop;
uint[nToks][nSetT + 1] SetT;
TokSet[nSet + 1] Set;
long ErrorCounter;
bool IsRepairMode;
bool LongErrorMsgs;
bool ParserTabIsLoaded;
IO.TextOut Out;

$

void ParserExpand()
{
    OpenRecStack RecStack1;
    long i;

    long ExpLen(long ArrayLen)
    {
        if (ArrayLen <= DIV(int.max, 2))
        {
            return 2 * ArrayLen;
        }
        else
        {
            HALT(99);
        }
    }

    if (RecTop >= RecStack.length)
    {
        NEW(RecStack1, ExpLen(RecStack.length));
        for (i = firstRecStack; i <= RecStack.length - 1; ++i)
        {
            RecStack1[i] = RecStack[i];
        }
        RecStack = RecStack1;
    }
}

void ReadParserTab(string Name)
{
    const magicNumber = 827092037;
    const tabTimeStamp = $;
    IO.File Tab;
    bool OpenError;
    int i;
    int j;
    long l;
    uint s;

    void LoadError(string Msg)
    {
        IO.WriteText(IO.Msg, "  loading the parser table ");
        IO.WriteString(IO.Msg, Name);
        IO.WriteText(IO.Msg, " failed\n");
        IO.WriteText(IO.Msg, "  ");
        IO.WriteText(IO.Msg, Msg);
        IO.WriteLn(IO.Msg);
        IO.Update(IO.Msg);
    }

    IO.OpenFile(Tab, Name, OpenError);
    if (OpenError)
    {
        LoadError("it could not be opened");
        return;
    }
    IO.GetLInt(Tab, l);
    if (l != magicNumber)
    {
        LoadError("no or corrupt parser table");
        return;
    }
    IO.GetLInt(Tab, l);
    if (l != tabTimeStamp)
    {
        LoadError("wrong time stamp");
        return;
    }
    IO.GetLInt(Tab, l);
    if (l != 31)
    {
        LoadError("incompatible MAX(SET) in table");
        return;
    }
    IO.GetSet(Tab, s);
    if (s != Set)
    {
        LoadError("incompatible SET format in table");
        return;
    }
    for (i = 0; i <= nSetT - 1; ++i)
    {
        for (j = 0; j <= nToks - 1; ++j)
        {
            IO.GetSet(Tab, SetT[i][j]);
        }
    }
    for (i = 0; i <= nSet - 1; ++i)
    {
        for (j = 0; j <= tokSetLen - 1; ++j)
        {
            IO.GetSet(Tab, Set[i][j]);
        }
    }
    IO.GetLInt(Tab, l);
    if (l != magicNumber)
    {
        LoadError("corrupt parser table");
        return;
    }
    ParserTabIsLoaded = true;
}

void ParserInit()
{
    RecTop = firstRecStack;
    ErrorCounter = 0;
    IsRepairMode = false;
    LongErrorMsgs = IO.IsOption("v");
}

void WriteTokSet(TokSet Toks)
{
    int Tok1;
    for (Tok1 = 0; Tok1 <= nToks - 1; ++Tok1)
    {
        if (MOD(Tok1, M) in Toks[DIV(Tok1, M)])
        {
            S.WriteRepr(IO.Msg, Tok1);
            IO.WriteText(IO.Msg, " ");
        }
    }
}

void ErrorMessageTok(IO.Position Pos, int Tok1)
{
    IO.WriteText(IO.Msg, "  ");
    IO.WritePos(IO.Msg, Pos);
    IO.WriteText(IO.Msg, "  syntax error, expected: ");
    S.WriteRepr(IO.Msg, Tok1);
    IO.WriteLn(IO.Msg);
    IO.Update(IO.Msg);
}

void ErrorMessageTokSet(IO.Position Pos, ref TokSet Toks)
{
    IO.WriteText(IO.Msg, "  ");
    IO.WritePos(IO.Msg, Pos);
    IO.WriteText(IO.Msg, "  syntax error, expected: ");
    WriteTokSet(Toks);
    IO.WriteLn(IO.Msg);
    IO.Update(IO.Msg);
}

void RestartMessage(IO.Position Pos)
{
    if (LongErrorMsgs)
    {
        IO.WriteText(IO.Msg, "  ");
        IO.WritePos(IO.Msg, Pos);
        IO.WriteText(IO.Msg, "      restart point\n");
        IO.Update(IO.Msg);
    }
}

void RepairMessage(IO.Position Pos, int Tok1)
{
    if (LongErrorMsgs)
    {
        IO.WriteText(IO.Msg, "  ");
        IO.WritePos(IO.Msg, Pos);
        IO.WriteText(IO.Msg, "      symbol inserted: ");
        S.WriteRepr(IO.Msg, Tok1);
        IO.WriteLn(IO.Msg);
        IO.Update(IO.Msg);
    }
}

void SkipTokens(int Recover)
{
    TokSet GlobalRecoverySet;
    int i;
    int j;
    GlobalRecoverySet = Set[Recover];
    for (i = firstRecStack; i <= RecTop - 1; ++i)
    {
        for (j = 0; j <= tokSetLen - 1; ++j)
        {
            GlobalRecoverySet[j] = GlobalRecoverySet[j] + Set[RecStack[i]][j];
        }
    }
    while (!(MOD(Tok, M) in GlobalRecoverySet[DIV(Tok, M)]))
    {
        S.Get(Tok);
    }
    RestartMessage(S.Pos);
    IsRepairMode = true;
}

void ErrorRecovery(int Expected, int Recover)
{
    if (!IsRepairMode)
    {
        ++ErrorCounter;
        ErrorMessageTokSet(S.Pos, Set[Expected]);
        SkipTokens(Recover);
    }
}

void RecoveryTerminal(int ExpectedTok, int Recover)
{
    if (!IsRepairMode)
    {
        ++ErrorCounter;
        ErrorMessageTok(S.Pos, ExpectedTok);
        SkipTokens(Recover);
    }
    if (Tok != ExpectedTok)
    {
        RepairMessage(S.Pos, ExpectedTok);
    }
    else
    {
        if (Tok != endTok)
        {
            S.Get(Tok);
        }
        IsRepairMode = false;
    }
}

$

void Compile()
{
    HeapType V1;
    if (ParserTabIsLoaded && EvalInitSucceeds() $)
    {
        IO.WriteText(IO.Msg, "$ compiler: compiling...\n");
        IO.Update(IO.Msg);
        ParserInit;
        S.Init;
        S.Get(Tok);
        $(V1);
        $
    }
    else if (!ParserTabIsLoaded)
    {
        IO.WriteText(IO.Msg, "parser table is not loaded\n");
        IO.Update(IO.Msg);
    }
}

static this()
{
    IO.WriteText(IO.Msg, "$ compiler (generated with Epsilon)\n");
    IO.Update(IO.Msg);
    NEW(RecStack, 500);
    ParserTabIsLoaded = false;
    ReadParserTab("$");
    Reset;
}

$

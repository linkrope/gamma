module $;

import runtime;
import std.stdio;
import IO = eIO;
import Sets = eSets;
import S = $;
import io : Position, TextIn;
import std.stdio;

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
    long ExpLen(long ArrayLen)
    {
        if (ArrayLen <= DIV(int.max, 2))
        {
            return 2 * ArrayLen;
        }
        else
        {
            assert(0);
        }
    }

    if (RecTop >= RecStack.length)
    {
        OpenRecStack RecStack1 = new int[ExpLen(RecStack.length)];

        for (size_t i = firstRecStack; i < RecStack.length; ++i)
        {
            RecStack1[i] = RecStack[i];
        }
        RecStack = RecStack1;
    }
}

void ReadParserTab(string Name)
{
    const magicNumber = 827_092_037;
    const tabTimeStamp = $;
    IO.File Tab;
    bool OpenError;
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
    if (s != Sets.SET(0, 2, 3, 6, 9, 13, 18, 19, 20, 24, 25, 27, 28, 31))
    {
        LoadError("incompatible SET format in table");
        return;
    }
    for (size_t i = 0; i < nSetT; ++i)
    {
        for (size_t j = 0; j < nToks; ++j)
        {
            IO.GetSet(Tab, SetT[i][j]);
        }
    }
    for (size_t i = 0; i < nSet; ++i)
    {
        for (size_t j = 0; j < tokSetLen; ++j)
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
    LongErrorMsgs = IO.IsOption('v');
}

void WriteTokSet(TokSet Toks)
{
    for (int Tok1 = 0; Tok1 <= nToks - 1; ++Tok1)
    {
        if (Sets.IN(Toks[DIV(Tok1, M)], MOD(Tok1, M)))
        {
            S.WriteRepr(IO.Msg, Tok1);
            IO.WriteText(IO.Msg, " ");
        }
    }
}

void ErrorMessageTok(Position Pos, int Tok1)
{
    writeln;
    writeln(Pos);
    IO.WriteText(IO.Msg, "  syntax error, expected: ");
    S.WriteRepr(IO.Msg, Tok1);
    IO.WriteLn(IO.Msg);
    IO.Update(IO.Msg);
}

void ErrorMessageTokSet(Position Pos, ref TokSet Toks)
{
    writeln;
    writeln(Pos);
    IO.WriteText(IO.Msg, "  syntax error, expected: ");
    WriteTokSet(Toks);
    IO.WriteLn(IO.Msg);
    IO.Update(IO.Msg);
}

void RestartMessage(Position Pos)
{
    if (LongErrorMsgs)
    {
        writeln;
        writeln(Pos);
        IO.WriteText(IO.Msg, "      restart point\n");
        IO.Update(IO.Msg);
    }
}

void RepairMessage(Position Pos, int Tok1)
{
    if (LongErrorMsgs)
    {
        writeln;
        writeln(Pos);
        IO.WriteText(IO.Msg, "      symbol inserted: ");
        S.WriteRepr(IO.Msg, Tok1);
        IO.WriteLn(IO.Msg);
        IO.Update(IO.Msg);
    }
}

void SkipTokens(int Recover)
{
    TokSet GlobalRecoverySet = Set[Recover];

    for (size_t i = firstRecStack; i <= RecTop - 1; ++i)
    {
        for (size_t j = 0; j <= tokSetLen - 1; ++j)
        {
            GlobalRecoverySet[j] = GlobalRecoverySet[j] + Set[RecStack[i]][j];
        }
    }
    while (!Sets.IN(GlobalRecoverySet[DIV(Tok, M)], MOD(Tok, M)))
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
void main(string[] args)
{
    import core.stdc.stdlib : exit, EXIT_FAILURE, EXIT_SUCCESS;
    import std.exception : ErrnoException;
    import std.getopt : defaultGetoptPrinter, getopt, GetoptResult;
    import std.range : dropOne, empty, front;

    bool info;
    bool verbose;
    bool write;
    GetoptResult result;

    try
    {
        result = getopt(args,
                "info|i", "Show heap usage information.", &info,
                "verbose|v", "Print verbose parser error messages.", &verbose,
                "write|w", "Toggle default for writing output.", &write,
        );
    }
    catch (Exception exception)
    {
        stderr.writefln!"error: %s"(exception.msg);
        exit(EXIT_FAILURE);
    }
    if (result.helpWanted)
    {
        import std.path : baseName;

        writefln!"Usage: %s [options] <file>..."(args.front.baseName);
        writeln("Compile each file.");
        defaultGetoptPrinter("Options:", result.options);
        exit(EXIT_SUCCESS);
    }

    IO.option['i'] = info;
    IO.option['v'] = verbose;
    IO.option['w'] = write;

    if (args.dropOne.empty)
        Compile(TextIn("stdin", stdin));

    try
    {
        foreach (arg; args.dropOne)
            Compile(TextIn(arg));
    }
    catch (ErrnoException exception)
    {
        stderr.writefln!"error: %s"(exception.msg);
        exit(EXIT_FAILURE);
    }

}

void Compile(TextIn textIn)
{
    HeapType V1;

    if (ParserTabIsLoaded && EvalInitSucceeds()$)
    {
        IO.WriteText(IO.Msg, "$ compiler: compiling...\n");
        IO.Update(IO.Msg);
        ParserInit;
        S.Init(textIn);
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
    RecStack = new int[500];
    ParserTabIsLoaded = false;
    ReadParserTab("$");
    Reset;
}

// END $.
$

module $;

import IO = eIO;
import io : Position, TextIn;
import runtime;
import std.stdio;
import S = $;

const nToks = $;
const tokSetLen = $;
const nSetT = $;
const nSet = $;
enum M = size_t.sizeof * 8;
const endTok = 0;
const sepTok = 2;
const firstRecStack = 1;
alias OpenRecStack = int[];
alias TokSet = size_t[tokSetLen];
int Tok;
OpenRecStack RecStack;
int RecTop;
size_t[nToks][nSetT + 1] SetT;
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

void ReadParserTab(string name)
{
    const magicNumber = 827_092_037;
    const tabTimeStamp = $;
    IO.File Tab;
    bool OpenError;
    long l;
    size_t s;

    void LoadError(string Msg)
    {
        IO.Msg.write("  loading the parser table ");
        IO.Msg.write(name);
        IO.Msg.write(" failed\n");
        IO.Msg.write("  ");
        IO.Msg.write(Msg);
        IO.Msg.writeln;
        IO.Msg.flush;
    }

    IO.OpenFile(Tab, name, OpenError);
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
    if (l != M)
    {
        LoadError("incompatible MAX(SET) in table");
        return;
    }
    IO.GetSet(Tab, s);
    if (s != 0b10110010_01000100_00111000_11011001)
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
    for (int Tok1 = 0; Tok1 < nToks; ++Tok1)
    {
        if (Toks[DIV(Tok1, M)] & 1uL << MOD(Tok1, M))
        {
            S.WriteRepr(IO.Msg, Tok1);
            IO.Msg.write(" ");
        }
    }
}

void ErrorMessageTok(Position Pos, int Tok1)
{
    writeln;
    writeln(Pos);
    IO.Msg.write("  syntax error, expected: ");
    S.WriteRepr(IO.Msg, Tok1);
    IO.Msg.writeln;
    IO.Msg.flush;
}

void ErrorMessageTokSet(Position Pos, ref TokSet Toks)
{
    writeln;
    writeln(Pos);
    IO.Msg.write("  syntax error, expected: ");
    WriteTokSet(Toks);
    IO.Msg.writeln;
    IO.Msg.flush;
}

void RestartMessage(Position Pos)
{
    if (LongErrorMsgs)
    {
        writeln;
        writeln(Pos);
        IO.Msg.write("      restart point\n");
        IO.Msg.flush;
    }
}

void RepairMessage(Position Pos, int Tok1)
{
    if (LongErrorMsgs)
    {
        writeln;
        writeln(Pos);
        IO.Msg.write("      symbol inserted: ");
        S.WriteRepr(IO.Msg, Tok1);
        IO.Msg.writeln;
        IO.Msg.flush;
    }
}

void SkipTokens(int Recover)
{
    TokSet GlobalRecoverySet = Set[Recover];

    for (size_t i = firstRecStack; i < RecTop; ++i)
    {
        for (size_t j = 0; j < tokSetLen; ++j)
            GlobalRecoverySet[j] = GlobalRecoverySet[j] + Set[RecStack[i]][j];
    }
    while (!(GlobalRecoverySet[DIV(Tok, M)] & 1uL << MOD(Tok, M)))
        S.Get(Tok);
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
        IO.Msg.write("$ compiler: compiling...\n");
        IO.Msg.flush;
        ParserInit;
        S.Init(textIn);
        S.Get(Tok);
        $(V1);
        $
    }
    else if (!ParserTabIsLoaded)
    {
        IO.Msg.write("parser table is not loaded\n");
        IO.Msg.flush;
    }
}

static this()
{
    IO.Msg.write("$ compiler (generated with Epsilon)\n");
    IO.Msg.flush;
    RecStack = new int[500];
    ParserTabIsLoaded = false;
    ReadParserTab("$");
    Reset;
}

// END $.
$

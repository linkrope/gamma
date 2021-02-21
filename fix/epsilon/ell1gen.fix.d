module $;

import IO = epsilon.io : TextOut;
import io : Input, Position, read;
import log;
import runtime;
// import std.stdio;
import S = $;

const nToks = $;
const tokSetLen = $;
const nSetT = $;
const nSet = $;
enum M = size_t.sizeof * 8;
const endTok = 0;
const sepTok = 2;
const firstRecStack = 1;
alias TokSet = size_t[tokSetLen];
int Tok;
int[] RecStack;
int RecTop;
size_t[nToks][nSetT + 1] SetT;
TokSet[nSet + 1] Set;
long ErrorCounter;
bool IsRepairMode;
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
        auto RecStack1 = new int[ExpLen(RecStack.length)];

        for (size_t i = firstRecStack; i < RecStack.length; ++i)
        {
            RecStack1[i] = RecStack[i];
        }
        RecStack = RecStack1;
    }
}

void ReadParserTab(string name)
{
    import std.exception : ErrnoException;
    import std.stdio : File;

    const magicNumber = 827_092_037;
    const tabTimeStamp = $;
    File Tab;
    long l;
    size_t s;

    void LoadError(string message)
    {
        error!"loading parser table %s failed: %s"(name, message);
    }

    try
    {
        Tab = File(name, "r");
    }
    catch (ErrnoException)
    {
        LoadError("cannot be opened");
        return;
    }
    Tab.readf!"long %s\n"(l);
    if (l != magicNumber)
    {
        LoadError("no or corrupt parser table");
        return;
    }
    Tab.readf!"long %s\n"(l);
    if (l != tabTimeStamp)
    {
        LoadError("wrong time stamp");
        return;
    }
    Tab.readf!"long %s\n"(l);
    if (l != M)
    {
        LoadError("incompatible MAX(SET) in table");
        return;
    }
    Tab.readf!"set %s\n"(s);
    if (s != 0b10110010_01000100_00111000_11011001)
    {
        LoadError("incompatible SET format in table");
        return;
    }
    for (size_t i = 0; i < nSetT; ++i)
        for (size_t j = 0; j < nToks; ++j)
            Tab.readf!"set %s\n"(SetT[i][j]);
    for (size_t i = 0; i < nSet; ++i)
        for (size_t j = 0; j < tokSetLen; ++j)
            Tab.readf!"set %s\n"(Set[i][j]);
    Tab.readf!"long %s\n"(l);
    if (l != magicNumber)
    {
        LoadError("corrupt parser table");
        return;
    }
    ParserTabIsLoaded = true;
    Tab.close;
}

void ParserInit()
{
    RecTop = firstRecStack;
    ErrorCounter = 0;
    IsRepairMode = false;
}

void ErrorMessageTok(Position Pos, int Tok1)
{
    error!"syntax error, expected: %s\n%s"(S.Repr(Tok1), Pos);
}

void ErrorMessageTokSet(Position Pos, ref TokSet Toks)
{
    string[] items;

    for (int Tok1 = 0; Tok1 < nToks; ++Tok1)
        if (Toks[DIV(Tok1, M)] & 1uL << MOD(Tok1, M))
            items ~= S.Repr(Tok1);
    error!"syntax error, expected: %-(%s, %)\n%s"(items, Pos);
}

void RestartMessage(Position Pos)
{
    trace!"restart point\n%s"(Pos);
}

void RepairMessage(Position Pos, int Tok1)
{
    trace!"symbol inserted: %s\n%s"(S.Repr(Tok1), Pos);
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
    import std.stdio : stdin, writefln, writeln;

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
        error!"%s"(exception.msg);
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

    if (verbose)
        levels |= Level.trace;
    if (args.dropOne.empty)
        Compile(read("stdin", stdin), info, verbose, write);

    try
    {
        foreach (arg; args.dropOne)
            Compile(read(arg), info, verbose, write);
    }
    catch (ErrnoException exception)
    {
        error!"%s"(exception.msg);
        exit(EXIT_FAILURE);
    }

}

void Compile(Input input, bool info_, bool verbose, bool write)
{
    HeapType V1;

    if (ParserTabIsLoaded && EvalInitSucceeds()$)
    {
        trace!"$ compiler: compiling...";
        ParserInit;
        S.Init(input);
        S.Get(Tok);
        $(V1);
        $
    }
}

static this()
{
    info!"$ compiler (generated with epsilon)";
    RecStack = new int[500];
    ParserTabIsLoaded = false;
    ReadParserTab("$");
    Reset;
}

// END $.
$

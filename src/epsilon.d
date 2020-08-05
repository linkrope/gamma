module epsilon;

import runtime;
import std.stdio;

void main(string[] args)
{
    import core.stdc.stdlib : exit, EXIT_FAILURE, EXIT_SUCCESS;
    import std.exception : ErrnoException;
    import std.getopt : defaultGetoptPrinter, getopt, GetoptResult;
    import std.range : dropOne, empty, front;
    import std.stdio : stderr, writefln, writeln;
    import IO = eIO;

    bool c, dR, m, p, r;
    bool space;
    bool sweep;
    bool verbose;
    bool write;
    GetoptResult result;

    try
    {
        result = getopt(args,
                "c", "Disable collapsing constant trees.", &c,
                "dR", "Debug reference counting.", &dR,
                "m", "Modules are shown, not compiled directly.", &m,
                "p", "Parser ignores regular token marks at hyper-nonterminals.", &p,
                "r", "Disable reference counting in compiled compiler.", &r,
                "space|s", "Compiled compiler uses space instead of newline as separator.", &space,
                "sweep", "Compile single-sweep evaluator.", &sweep,
                "verbose|v", "Print debug output.", &verbose,
                "write|w", "Write compilation output as default.", &write,
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
        writeln("Compile each Extended Affix Grammar file into a compiler.");
        defaultGetoptPrinter("Options:", result.options);
        exit(EXIT_SUCCESS);
    }

    IO.option['c'] = c;
    IO.option['m'] = m;
    IO.option['p'] = p;
    IO.option['r'] = r;
    IO.option['s'] = space;
    IO.option['v'] = verbose;
    IO.option['w'] = write;
    IO.longOption['d']['R'] = dR;

    if (args.dropOne.empty)
        compile(stdin, sweep);

    try
    {
        foreach (arg; args.dropOne)
            compile(File(arg), sweep);
    }
    catch (ErrnoException exception)
    {
        stderr.writefln!"error: %s"(exception.msg);
        exit(EXIT_FAILURE);
    }
}

void compile(File file, bool sweep)
{
    import std.range : empty;
    import Analyser = eAnalyser;
    import EAG = eEAG;
    import ELL1Gen = eELL1Gen;
    import IO = eIO;
    import Predicates = ePredicates;
    import ScanGen = eScanGen;
    import Scanner = eScanner;
    import SLEAGGen = eSLEAGGen;
    import SSweep = eSSweep;

    Analyser.Analyse(file);
    Analyser.Warnings;
    Predicates.Check;
    if (IO.IsOption('v'))
        Predicates.List;
    ELL1Gen.Test;

    bool success = false;

    if (!sweep)
    {
        SLEAGGen.Test;
        if (IN(EAG.History, EAG.isSLEAG))
        {
            ScanGen.Generate;
            ELL1Gen.Generate;
            success = true;
        }
    }
    if (!success)
    {
        SSweep.Test;
        if (IN(EAG.History, EAG.isSSweep))
        {
            ScanGen.Generate;
            SSweep.Generate;
            ELL1Gen.GenerateParser;
            success = true;
        }
    }
    if (success)
    {
        build(IO.files);
        IO.files = null;
    }
}

void build(string[] files)
{
    import core.stdc.stdlib : exit;
    import std.string : join;
    import std.process : spawnProcess, wait;

    const args = "dmd" ~ files ~ "include/runtime.d" ~ "src/eIO.d";

    writefln!"%s"(args.join(' '));

    auto pid = spawnProcess(args);
    const status = wait(pid);

    if (status)
        exit(status);
}

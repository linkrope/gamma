module epsilon;

import io : TextIn;
import runtime;
import std.stdio;

void main(string[] args)
{
    import core.stdc.stdlib : exit, EXIT_FAILURE, EXIT_SUCCESS;
    import IO = eIO;
    import std.exception : ErrnoException;
    import std.getopt : defaultGetoptPrinter, getopt, GetoptResult;
    import std.range : dropOne, empty, front;
    import std.stdio : stderr, writefln, writeln;

    bool c, dR, m, o, p, r;
    bool space;
    bool verbose;
    bool write;
    bool sweep;
    bool soag;
    GetoptResult result;

    try
    {
        result = getopt(args,
                "c", "Disable collapsing constant trees.", &c,
                "dR", "Debug reference counting.", &dR,
                "m", "Modules are shown, not compiled directly.", &m,
                "p", "Parser ignores regular token marks at hyper-nonterminals.", &p,
                "o", "Disable optimizing of variable storage in compiled compiler.", &o,
                "r", "Disable reference counting in compiled compiler.", &r,
                "space|s", "Compiled compiler uses space instead of newline as separator.", &space,
                "verbose|v", "Print debug output.", &verbose,
                "write|w", "Write compilation output as default.", &write,
                "sweep", "Compile single-sweep evaluator.", &sweep,
                "soag", "Compile SOAG evaluator.", &soag,
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
    IO.option['o'] = o;
    IO.option['p'] = p;
    IO.option['r'] = r;
    IO.option['s'] = space;
    IO.option['v'] = verbose;
    IO.option['w'] = write;
    IO.longOption['d']['R'] = dR;

    if (verbose)
    {
        import log : Level, levels;

        levels |= Level.trace;
    }
    if (args.dropOne.empty)
        compile(TextIn("stdin", stdin), sweep, soag);

    try
    {
        foreach (arg; args.dropOne)
            compile(TextIn(arg), sweep, soag);
    }
    catch (ErrnoException exception)
    {
        stderr.writefln!"error: %s"(exception.msg);
        exit(EXIT_FAILURE);
    }
    catch (Exception exception)
    {
        exit(EXIT_FAILURE);
    }
}

void compile(TextIn textIn, bool sweep, bool soag)
{
    import Analyser = eAnalyser;
    import EAG = eEAG;
    import ELL1Gen = eELL1Gen;
    import IO = eIO;
    import Predicates = ePredicates;
    import ScanGen = eScanGen;
    import Scanner = eScanner;
    import Sets = eSets;
    import SLEAGGen = eSLEAGGen;
    import SSweep = eSSweep;
    import SOAGGen = soag.eSOAGGen;
    import std.exception : enforce;
    import std.range : empty;

    Analyser.Analyse(textIn);

    enforce(Analyser.ErrorCounter == 0,
            "analyser errors");

    Analyser.Warnings;
    Predicates.Check;
    if (IO.IsOption('v'))
        Predicates.List;
    ELL1Gen.Test;

    bool success = false;

    if (!sweep && !soag)
    {
        SLEAGGen.Test;
        if (Sets.IN(EAG.History, EAG.isSLEAG))
        {
            ScanGen.Generate;
            ELL1Gen.Generate;
            success = true;
        }
    }
    if (!success && !soag)
    {
        SSweep.Test;
        if (Sets.IN(EAG.History, EAG.isSSweep))
        {
            ScanGen.Generate;
            SSweep.Generate;
            ELL1Gen.GenerateParser;
            success = true;
        }
    }
    if (!success)
    {
        ScanGen.Generate;
        SOAGGen.Generate;
        if (IO.IsOption('v'))
        {
            import SOAGProtocol = soag.eSOAGProtocol;

            SOAGProtocol.WriteRulesL4;
            SOAGProtocol.WriteSyms;
        }
        ELL1Gen.GenerateParser;
        success = true;
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
    import std.process : spawnProcess, wait;
    import std.string : join;

    const args = "dmd" ~ files ~ "-g"
        ~ "include/runtime.d" ~ "src/eIO.d" ~ "src/eSets.d" ~ "src/io.d" ~ "src/soag/eLIStacks.d";

    writefln!"%s"(args.join(' '));

    auto pid = spawnProcess(args);
    const status = wait(pid);

    if (status)
        exit(status);
}

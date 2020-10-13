module epsilon.main;

import epsilon.settings;
import io : TextIn;
import runtime;
import std.stdio;

void main(string[] args)
{
    import core.stdc.stdlib : exit, EXIT_FAILURE, EXIT_SUCCESS;
    import std.exception : ErrnoException;
    import std.getopt : defaultGetoptPrinter, getopt, GetoptResult;
    import std.range : dropOne, empty, front;
    import std.stdio : stderr, writefln, writeln;

    GetoptResult result;
    Settings settings;

    try
    {
        with (settings)
        {
            result = getopt(args,
                    "c", "Disable collapsing constant trees.", &c,
                    "dR", "Debug reference counting.", &dR,
                    "m", "Modules are shown, not compiled directly.", &showMod,
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

    if (settings.verbose)
    {
        import log : Level, levels;

        levels |= Level.trace;
    }
    if (args.dropOne.empty)
        compile(TextIn("stdin", stdin), settings);

    try
    {
        foreach (arg; args.dropOne)
            compile(TextIn(arg), settings);
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

void compile(TextIn textIn, Settings settings)
{
    import Analyser = eAnalyser;
    import EAG = eEAG;
    import ELL1Gen = eELL1Gen;
    import IO = eIO;
    import Predicates = ePredicates;
    import ScanGen = eScanGen;
    import Scanner = eScanner;
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
    if (settings.verbose)
        Predicates.List;
    ELL1Gen.Test(settings);

    bool success = false;

    if (!(settings.sweep || settings.soag))
    {
        SLEAGGen.Test;
        if (EAG.History & EAG.isSLEAG)
        {
            ScanGen.Generate(settings);
            ELL1Gen.Generate(settings);
            success = true;
        }
    }
    if (!(success || settings.soag))
    {
        SSweep.Test(settings);
        if (EAG.History & EAG.isSSweep)
        {
            ScanGen.Generate(settings);
            SSweep.Generate(settings);
            ELL1Gen.GenerateParser(settings);
            success = true;
        }
    }
    if (!success)
    {
        ScanGen.Generate(settings);
        SOAGGen.Generate(settings);
        if (settings.verbose)
        {
            import SOAGProtocol = soag.eSOAGProtocol;

            SOAGProtocol.WriteRulesL4;
            SOAGProtocol.WriteSyms;
        }
        ELL1Gen.GenerateParser(settings);
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

    const args = "dmd" ~ files ~ "-g" ~ "include/runtime.d"
        ~ "src/eIO.d" ~ "src/io.d" ~ "src/log.d" ~ "src/soag/eLIStacks.d";

    writefln!"%s"(args.join(' '));

    auto pid = spawnProcess(args);
    const status = wait(pid);

    if (status)
        exit(status);
}

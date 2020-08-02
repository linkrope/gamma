module epsilon;

import std.stdio;

void main(string[] args)
{
    import core.stdc.stdlib : exit, EXIT_FAILURE, EXIT_SUCCESS;
    import std.getopt : defaultGetoptPrinter, getopt, GetoptResult;
    import std.range : dropOne, empty, front;
    import std.stdio : stderr, writefln, writeln;

    bool verbose;
    GetoptResult result;

    try
    {
        result = getopt(args,
                "verbose|v", "Print debug output.", &verbose,
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

    if (args.dropOne.empty)
        compile(stdin, verbose);

    foreach (arg; args.dropOne)
        compile(File(arg), verbose);
}

void compile(File file, bool verbose)
{
    import Analyser = eAnalyser;
    import ELL1Gen = eELL1Gen;
    import IO = eIO;
    import Predicates = ePredicates;
    import ScanGen = eScanGen;
    import Scanner = eScanner;
    import SLEAGGen = eSLEAGGen;

    IO.option['m'] = false; // -m: modules are shown, not compiled directly
    IO.option['p'] = false; // -p: parser ignores regular token marks at Hypernonterminals
    Scanner.verbose = verbose;

    Analyser.Analyse(file);
    Analyser.Warnings;
    Predicates.Check;
    if (verbose)
        Predicates.List;
    ELL1Gen.Test;
    SLEAGGen.Test;

    ScanGen.Generate;
    ELL1Gen.Generate;

    build(IO.files);
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

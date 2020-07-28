module epsilon;

import Analyser = eAnalyser;
import Scanner = eScanner;

void main(string[] args)
{
    import core.stdc.stdlib : exit, EXIT_FAILURE, EXIT_SUCCESS;
    import std.exception : enforce;
    import std.getopt : defaultGetoptPrinter, getopt, GetoptResult;
    import std.range : dropOne, front;
    import std.stdio : stderr, writefln, writeln;

    bool verbose;
    GetoptResult result;

    try
    {
        result = getopt(args,
                "verbose|v", "Print debug output.", &verbose,
        );
        enforce(args.dropOne.length == 1,
                "exactly one file is required");
    }
    catch (Exception exception)
    {
        stderr.writefln!"error: %s"(exception.msg);
        exit(EXIT_FAILURE);
    }
    if (result.helpWanted)
    {
        import std.path : baseName;

        writefln!"Usage: %s [options] file"(args.front.baseName);
        writeln("Compile the Extended Affix Grammar file into a compiler.");
        defaultGetoptPrinter("Options:", result.options);
        exit(EXIT_SUCCESS);
    }

    const file = args.dropOne.front;

    Scanner.verbose = verbose;
    Analyser.Analyse(file);
    Analyser.Warnings;
}

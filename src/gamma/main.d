module gamma.main;

import log;
import std.range;
import std.stdio;

void main(string[] args)
{
    import core.stdc.stdlib : exit, EXIT_FAILURE, EXIT_SUCCESS;
    import gamma.grammar.hyper.PrintingHyperVisitor : printingHyperVisitor;
    import gamma.input.epsilang.Analyzer : Analyzer;
    import std.datetime.stopwatch : AutoStart, StopWatch;
    import std.exception : ErrnoException;
    import std.getopt : defaultGetoptPrinter, getopt, GetoptResult;

    GetoptResult result;
    bool verbose;

    try
    {
        result = getopt(args,
                "verbose|v", "Print debug output.", &verbose,
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
        writeln("Compile each Extended Affix Grammar file into a compiler.");
        defaultGetoptPrinter("Options:", result.options);
        exit(EXIT_SUCCESS);
    }

    if (verbose)
        levels |= Level.trace;

    try
    {
        foreach (arg; args.dropOne)
        {
            auto stopWatch = StopWatch(AutoStart.yes);
            auto input = File(arg);
            auto analyzer = new Analyzer(input);

            analyzer.parseSpecification;

            const errorCount = analyzer.getErrorCount;

            switch (errorCount)
            {
                case 0:
                    if (auto grammar = analyzer.yieldHyperGrammar)
                    {
                        auto visitor = printingHyperVisitor(stdout.lockingTextWriter);

                        visitor.visit(analyzer.yieldHyperGrammar);
                    }
                    break;
                case 1:
                    stderr.writeln("1 error");
                    break;
                default:
                    stderr.writeln(errorCount, " errors");
                    break;
            }

            stopWatch.stop;
            stdout.writeln(stopWatch.peek.total!"msecs", " milliseconds");
        }
    }
    catch (ErrnoException exception)
    {
        stderr.writeln(exception.msg);
        assert(0);
    }
}

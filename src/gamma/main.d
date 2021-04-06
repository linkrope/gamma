module gamma.main;

import gamma.grammar.Grammar;
import log;
import std.range;
import std.stdio;

void main(string[] args)
{
    import core.stdc.stdlib : exit, EXIT_FAILURE, EXIT_SUCCESS;
    import gamma.grammar.hyper.PrintingHyperVisitor : printingHyperVisitor;
    import gamma.grammar.Node : Node;
    import gamma.grammar.PrintingVisitor : printingVisitor;
    import gamma.grammar.Symbol : Symbol;
    import gamma.input.epsilang.Analyzer : Analyzer;
    import gamma.parsgen.lalr1.ParserGrammarBuilder : extendedCfgFromHyperGrammar;
    import gamma.parsgen.lalr1.PredicateFilter : PredicateFilter;
    import std.algorithm : map;
    import std.array : assocArray;
    import std.datetime.stopwatch : AutoStart, StopWatch;
    import std.exception : ErrnoException;
    import std.getopt : defaultGetoptPrinter, getopt, GetoptResult;
    import std.typecons : tuple;

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

            info!"compiling %s"(arg);
            analyzer.parseSpecification;

            const errorCount = analyzer.getErrorCount;

            switch (errorCount)
            {
                case 0:
                    if (auto grammar = analyzer.yieldMetaGrammar)
                    {
                        auto visitor = printingVisitor(stdout.lockingTextWriter);

                        visitor.visit(grammar);
                        stdout.writeln;
                    }
                    else
                        stderr.writeln("meta grammar not well defined");
                    if (auto grammar = analyzer.yieldHyperGrammar)
                    {
                        bool[Symbol] lexicalHyperNonterminals = analyzer.getLexicalHyperNonterminals.byKeyValue
                            .map!(pair => tuple(cast(Symbol) pair.key, pair.value))
                            .assocArray;
                        auto predicateFilter = new class PredicateFilter
                        {
                            override bool isPredicate(Node node)
                            {
                                return false;
                            }
                        };
                        auto parserGrammar = grammar
                            .extendedCfgFromHyperGrammar(lexicalHyperNonterminals, predicateFilter);
                        auto visitor = printingHyperVisitor(stdout.lockingTextWriter);

                        visitor.visit(parserGrammar);
                        generateParser(parserGrammar);
                    }
                    else
                        stderr.writeln("hyper grammar not well defined");
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
        exit(EXIT_FAILURE);
    }
}

private void generateParser(Grammar grammar)
{
    import gamma.parsgen.lalr1.PennelloDeRemer : PennelloDeRemer;
    import gamma.parsgen.lalr1.SimpleLR1ConflictResolver : SimpleLR1ConflictResolver;
    import gamma.parsgen.lalr1.LR1ParserTablesWriter : write;
    import std.stdio : stdout;

    auto parserGenerator = new PennelloDeRemer;
    auto conflictResolver = new SimpleLR1ConflictResolver(grammar);
    auto parserTables = parserGenerator.computeParser(grammar, conflictResolver);

    write(parserTables, stdout);
}

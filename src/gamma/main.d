//          Copyright Mario Kröplin 2022.
// Distributed under the Boost Software License, Version 1.0.
//    (See accompanying file LICENSE_1_0.txt or copy at
//          https://www.boost.org/LICENSE_1_0.txt)

module gamma.main;

import argparse;
import epsilon.settings;
import gamma.grammar.Grammar;
import io : Input, read;
import log;
import runtime;
import std.range;
import std.stdio;

mixin CLI!(config, Arguments).main!command;

Config config()
{
    Config config;

    config.bundling = true;
    return config;
}

@(Command(null).Description("Compile each Extended Affix Grammar FILE into a compiler"))
struct Arguments
{
    @(PositionalArgument(0).Optional().Placeholder("FILE").Description("Extended-Affix Grammar FILE"))
    string[] files;

    @(NamedArgument.Description("Disable collapsing constant trees"))
    bool c;

    @(NamedArgument("g").Description("Generate only, do not compile"))
    bool generate;

    @(NamedArgument.Description("Disable optimizing of variable storage in compiled compiler"))
    bool o;

    @(NamedArgument.Description("Parser ignores regular token marks at hyper-nonterminals"))
    bool p;

    @(NamedArgument.Description("Disable reference counting in compiled compiler"))
    bool r;

    @(NamedArgument("s", "space").Description("Compiled compiler uses space instead of newline as separator"))
    bool space;

    @(NamedArgument("v", "verbose").Description("Print debug output"))
    bool verbose;

    @(NamedArgument("w", "write").Description("Write compilation output as default"))
    bool write;

    @(NamedArgument.Description("Generate LALR parser (experimental)"))
    bool lalr;

    @(NamedArgument.Description("Generate SLAG evaluator"))
    bool slag;

    @(NamedArgument.Description("Generate single-sweep evaluator"))
    bool sweep;

    @(NamedArgument.Description("Generate SOAG evaluator"))
    bool soag;

    @(NamedArgument("output-directory").Placeholder("DIRECTORY").Description("Write compiled compiler to DIRECTORY"))
    string outputDirectory;

    @(NamedArgument.Description("Show error positions language-server friendly as offsets"))
    bool offset;
}

void command(Arguments arguments)
{
    import core.stdc.stdlib : exit, EXIT_FAILURE;
    import std.exception : ErrnoException;

    with (arguments)
    {
        if (verbose)
            levels |= Level.trace;

        if (!slag && !sweep && !soag)
        {
            // try all evaluators until one fits
            slag = true;
            sweep = true;
            soag = true;
        }
        if (!outputDirectory.empty)
        {
            import std.file : mkdirRecurse;

            mkdirRecurse(outputDirectory);
        }
    }
    try
    {
        import std.typecons : No, Yes;

        const offset = arguments.offset ? Yes.offset : No.offset;

        if (arguments.files.empty)
            compile(read("stdin", stdin, offset), arguments);

        foreach (file; arguments.files)
            compile(read(file, offset), arguments);
    }
    catch (ErrnoException exception)
    {
        error!"%s"(exception.msg);
        exit(EXIT_FAILURE);
    }
    catch (Exception exception)
    {
        exit(EXIT_FAILURE);
    }
}

void compile(Input input, const Arguments arguments)
{
    import analyzer = epsilon.analyzer;
    import EAG = epsilon.eag;
    import ELL1Gen = epsilon.ell1gen;
    import LexGen = epsilon.lexgen;
    import Predicates = epsilon.predicates;
    import SLAGGen = epsilon.slaggen;
    import SOAGGen = epsilon.soag.soaggen;
    import Sweep = epsilon.sweep;
    import std.exception : enforce;

    if (arguments.lalr)
    {
        check(input, arguments);
        return;
    }

    const settings = createSettings(arguments);

    analyzer.Analyse(input);

    enforce(analyzer.ErrorCounter == 0);

    analyzer.CheckForUnreachableNonterminals;
    Predicates.Check;

    ELL1Gen.Test(settings);

    enforce(!ELL1Gen.Error);

    string[] fileNames;
    bool success = false;

    if (arguments.slag)
    {
        SLAGGen.Test;
        if (EAG.History & EAG.isSLAG)
        {
            fileNames = LexGen.Generate(settings) ~ fileNames;
            fileNames = ELL1Gen.Generate(settings) ~ fileNames;
            success = true;
        }
    }
    if (!success && arguments.sweep)
    {
        Sweep.Test(settings);
        if (EAG.History & EAG.isSweep)
        {
            fileNames = LexGen.Generate(settings) ~ fileNames;
            fileNames = Sweep.Generate(settings) ~ fileNames;
            fileNames = ELL1Gen.GenerateParser(settings) ~ fileNames;
            success = true;
        }
    }
    if (!success && arguments.soag)
    {
        fileNames = LexGen.Generate(settings) ~ fileNames;
        fileNames = SOAGGen.Generate(settings) ~ fileNames;
        if (arguments.verbose)
        {
            import protocol = epsilon.soag.protocol;

            protocol.WriteRulesL4;
            protocol.WriteSyms;
        }
        fileNames = ELL1Gen.GenerateParser(settings) ~ fileNames;
        success = true;
    }

    enforce(success);

    if (!fileNames.empty && !arguments.generate)
        build(fileNames, settings.outputDirectory);
}

// check hyper-grammar with new gamma Analyzer
void check(Input input, const Arguments arguments)
{
    import gamma.input.epsilang.Analyzer : Analyzer;
    import std.exception : enforce;

    auto analyzer = new Analyzer(input);

    analyzer.parseSpecification;

    const errorCount = analyzer.getErrorCount;

    enforce(errorCount == 0);

    auto metaGrammar = analyzer.yieldMetaGrammar;

    enforce(metaGrammar,
        "meta grammar not well defined");

    if (arguments.verbose)
    {
        import gamma.grammar.PrintingVisitor : printingVisitor;

        auto visitor = printingVisitor(stdout.lockingTextWriter);

        visitor.visit(metaGrammar);
        stdout.writeln;
    }

    auto hyperGrammar = analyzer.yieldHyperGrammar;

    enforce(hyperGrammar,
        "hyper grammar not well defined");

    if (arguments.verbose)
    {
        import gamma.grammar.hyper.PrintingHyperVisitor : printingHyperVisitor;

        auto visitor = printingHyperVisitor(stdout.lockingTextWriter);

        visitor.visit(hyperGrammar);
        stdout.writeln;
    }
    if (arguments.lalr)
    {
        import gamma.grammar.hyper.EBNFConverter : convert;
        import gamma.grammar.Node : Node;
        import gamma.grammar.Symbol : Symbol;
        import gamma.parsgen.lalr1.ParserGrammarBuilder : extendedCfgFromHyperGrammar;
        import gamma.parsgen.lalr1.PredicateFilter : PredicateFilter;
        import std.algorithm : map;
        import std.typecons : tuple;

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
        auto parserGrammar = hyperGrammar
            .convert
            .extendedCfgFromHyperGrammar(lexicalHyperNonterminals, predicateFilter);

        if (arguments.verbose)
        {
            import gamma.grammar.hyper.PrintingHyperVisitor : printingHyperVisitor;

            auto visitor = printingHyperVisitor(stdout.lockingTextWriter);

            visitor.visit(parserGrammar);
            stdout.writeln;
        }
        generateParser(parserGrammar);
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

Settings createSettings(const Arguments arguments) @nogc nothrow
{
    with (arguments)
    {
        Settings settings;

        settings.c = c;
        settings.o = o;
        settings.p = p;
        settings.r = r;
        settings.space = space;
        settings.write = write;
        settings.outputDirectory = outputDirectory;
        return settings;
    }
}

void build(string[] fileNames, string outputDirectory)
{
    import core.stdc.stdlib : exit;
    import std.format : format;
    import std.path : stripExtension;
    import std.process : spawnProcess, wait;
    import std.string : join;

    auto args = "dmd" ~ fileNames ~ "-g" ~ "include/runtime.d"
        ~ "src/io.d" ~ "src/log.d" ~ "src/epsilon/soag/listacks.d";

    if (!outputDirectory.empty)
    {
        args ~= format!"-od=%s"(outputDirectory);
        args ~= format!"-of=%s"(fileNames.front.stripExtension);
    }
    writefln!"%s"(args.join(' '));

    auto pid = spawnProcess(args);
    const status = wait(pid);

    if (status)
        exit(status);
}

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
        import std.stdio : stdin;
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

    check(input, arguments);
    if (arguments.lalr)
        return;

    const settings = createSettings(arguments);

    analyzer.Analyse(input);

    enforce(analyzer.ErrorCounter == 0);

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
    import gamma.input.epsilang.analyzer : Analyzer;

    auto analyzer = new Analyzer;

    analyzer.analyze(input);
    if (arguments.lalr)
    {
        import gamma.parsgen.lalr1.PennelloDeRemer : generateParser;

        generateParser(analyzer.parserGrammar);
    }
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
    import std.path : buildPath, stripExtension;
    import std.process : spawnProcess, wait;
    import std.string : join;

    auto args = "dmd" ~ fileNames ~ "-g" 
        ~ buildPath("include", "runtime.d")
        ~ buildPath("src", "io.d") 
        ~ buildPath("src", "log.d") 
        ~ buildPath("src", "epsilon", "soag", "listacks.d"); 

    if (!outputDirectory.empty)
    {
        args ~= format!"-od=%s"(outputDirectory);
        args ~= format!"-of=%s"(fileNames.front.stripExtension.executableName);
    }

    info!"%s"(args.join(' '));

    auto pid = spawnProcess(args);
    const status = wait(pid);

    if (status)
        exit(status);
}

string executableName(const string name)
{
    version(Windows)
        return name ~ ".exe";
    else
        return name;
}
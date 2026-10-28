//          Copyright Mario Kröplin 2025.
// Distributed under the Boost Software License, Version 1.0.
//    (See accompanying file LICENSE_1_0.txt or copy at
//          https://www.boost.org/LICENSE_1_0.txt)

module gamma.main;

import argparse;
import epsilon.eag : EpsilonEAG = EAG, epsilonEAG = eag;
import epsilon.settings;
import gamma.input.epsilang.analyzer : Analyzer, EAG;
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

    @(NamedArgument("runtime").Placeholder("DIRECTORY").Description("Use the gamma runtime package in DIRECTORY"))
    string runtime;

    @(NamedArgument.Description("Show error positions language-server friendly as offsets"))
    bool offset;

    @(NamedArgument.Description("Use dub to build compiled compiler"))
    bool dub;

    void validateOptions() const
    {
        import core.stdc.stdlib : exit, EXIT_FAILURE;
        import std.typecons : tuple;

        alias Conflict = tuple!("option1", "option2");

        static foreach (conflict; [
            Conflict("lalr", "slag"),
            Conflict("slag", "sweep"),
            Conflict("slag", "soag"),
            Conflict("sweep", "soag"),
        ])
        {
            if (__traits(getMember, this, conflict.option1)
                && __traits(getMember, this, conflict.option2))
            {
                error!"--%s cannot be combined with --%s"(conflict.option1, conflict.option2);
                exit(EXIT_FAILURE);
            }
        }
    }
}

void command(Arguments arguments)
{
    import core.stdc.stdlib : exit, EXIT_FAILURE;
    import std.exception : ErrnoException;

    arguments.validateOptions;
    with (arguments)
    {
        if (verbose)
            levels |= Level.trace;

        if (!slag && !sweep && !soag)
        {
            // try all evaluators until one fits
            slag = !lalr;
            sweep = true;
            soag = true;
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
    import ELL1Gen = epsilon.ell1gen;
    import LexGen = epsilon.lexgen;
    import Predicates = epsilon.predicates;
    import SLAGGen = epsilon.slaggen;
    import SOAGGen = epsilon.soag.soaggen;
    import Sweep = epsilon.sweep;
    import gamma.input.EAGBuilder : toEAG;
    import std.exception : enforce;

    const settings = createSettings(arguments);
    auto eag = (new Analyzer).analyze(input);

    epsilonEAG = eag.toEAG;

    if (arguments.lalr)
    {
        const fileNames = generateLRParser(epsilonEAG, eag, settings);

        settings.outputDirectory.generateRecipe(fileNames, arguments);

        if (!arguments.generate)
            settings.outputDirectory.build(fileNames, arguments);

        return;
    }

    Predicates.Check;

    const isELL1 = ELL1Gen.Test(settings);

    enforce(isELL1);

    string[] fileNames;
    bool success = false;

    if (arguments.slag)
    {
        const isSLAG = SLAGGen.Test;

        if (isSLAG)
        {
            fileNames = LexGen.Generate(settings) ~ fileNames;
            fileNames = ELL1Gen.Generate(settings) ~ fileNames;
            success = true;
        }
    }
    if (!success && arguments.sweep)
    {
        const isSweep = Sweep.Test(settings);

        if (isSweep)
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

    settings.outputDirectory.generateRecipe(fileNames, arguments);

    if (!arguments.generate)
        settings.outputDirectory.build(fileNames, arguments);
}

string[] generateLRParser(EpsilonEAG epsilonEAG, EAG eag, const Settings settings)
{
    import LexGen = epsilon.lexgen;
    import gamma.parsgen.lalr1.CodeGenerator : generateCode;
    import gamma.parsgen.lalr1.ParserGrammarBuilder : toParserGrammar;
    import gamma.parsgen.lalr1.PennelloDeRemer : generateParser;

    string[] fileNames = null;
    auto parserGrammar = eag.toParserGrammar;
    auto parserTables = generateParser(parserGrammar.grammar);

    fileNames ~= generateCode(epsilonEAG, parserTables, parserGrammar, settings);
    fileNames ~= LexGen.Generate(settings);

    return fileNames;
}

Settings createSettings(const Arguments arguments)
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
        settings.outputDirectory = outputDirectory.empty ? createTempDirectory : outputDirectory;
        return settings;
    }
}

string createTempDirectory()
{
    import std.file : mkdirRecurse, tempDir;
    import std.format : format;
    import std.path : buildPath;
    import std.process : thisProcessID;

    import std.stdio : writeln;

    const tempDirectory = buildPath(tempDir, format!"gamma-%s"(thisProcessID));

    trace!"using temp directory: %s"(tempDirectory);
    mkdirRecurse(tempDirectory);
    return tempDirectory;
}

void generateRecipe(const string outputDirectory, const string[] fileNames, const Arguments arguments)
{
    import std.algorithm : map;
    import std.file : write;
    import std.path : baseName, buildPath;
    import std.string : format, outdent, stripLeft;

    enum content = `
        {
            "name": "compiler",
            "targetName": "%s",
            "targetPath": %s,
            "targetType": "executable",
            "sourceFiles": [%(%s, %)],
            "stringImportPaths": ["."],
            "dependencies": {
                "gamma:runtime": %s
            }
        }
        `.outdent.stripLeft;
    const name = fileNames.front.baseName(".d");
    const outputPath = arguments.outputDirectory.empty ? "." : arguments.outputDirectory;
    buildPath(outputDirectory, "dub.json")
        .write(format!content(name, outputPath.jsonPathLiteral, fileNames.map!baseName, arguments.runtimeDependency));
}

string runtimeDependency(const Arguments arguments)
{
    import std.format : format;

    if (arguments.runtime.empty)
        return `"*"`;

    return format!`{"path": %s}`(arguments.runtime.jsonPathLiteral);
}

void build(const string outputDirectory, const string[] fileNames, const Arguments arguments)
{
    import core.stdc.stdlib : exit;
    import std.algorithm : map;
    import std.array : array;
    import std.format : format;
    import std.path : absolutePath, baseName, buildPath;
    import std.process : environment, spawnProcess, wait;

    string[] args;

    if (arguments.dub || arguments.lalr)
    {
        args = ["dub", "build"];
    }
    else
    {
        const compiler = environment.get("DC", "dmd");
        const name = fileNames.front.baseName(".d");
        const targetPath = absolutePath(arguments.outputDirectory.empty ? "." : arguments.outputDirectory);

        args = compiler ~ fileNames.map!baseName.array ~ "-g" ~ "-J."
            ~ absolutePath("include/runtime.d")
            ~ absolutePath("src/io.d") ~ absolutePath("src/log.d") ~ absolutePath("src/epsilon/soag/listacks.d")
            ~ format!"-of=%s"(buildPath(targetPath, name.executableName));
    }

    trace!"%-(%s %)"(args);

    const status = wait(spawnProcess(args, workDir: outputDirectory));

    if (status)
        exit(status);
}

string jsonPathLiteral(const string path)
{
    import std.json : JSONValue;
    import std.path : absolutePath, buildNormalizedPath;
    import std.string : tr;

    // use forward slashes so DUB can read Windows paths from JSON
    return JSONValue(path.absolutePath.buildNormalizedPath.tr(`\`, "/")).toString;
}

string executableName(const string name)
{
    import std.path : setExtension;

    version (Windows)
        return setExtension(name, "exe");
    else
        return name;
}

module gamma.parsgen.lalr1.CodeGenerator;

import epsilon.eag : EAG;
import epsilon.settings : Settings;
import gamma.parsgen.lalr1.FixWriter : includeFix;
import gamma.parsgen.lalr1.LexerGrammarBuilder : LexerGrammar;
import gamma.parsgen.lalr1.OrderedLR1Tables;
import gamma.parsgen.lalr1.ParserGrammarBuilder : ParserGrammar;

public string[] generateCode(EAG eag,
    OrderedLR1Tables parserTables, ParserGrammar parserGrammar,
    string evaluatorModuleName, string lexerTablesModuleName, Settings settings)
{
    with (generateEpsilonBridgeModule(eag, parserGrammar, settings))
        return generateLR1Modules(eag, parserTables, parserGrammar, moduleName, evaluatorModuleName,
            lexerTablesModuleName, settings)
            ~ fileName;
}

public auto generateLexerCode(OrderedLR1Tables lexerTables, LexerGrammar lexerGrammar,
    string compilerName, Settings settings)
{
    import gamma.parsgen.lalr1.LR1TablesWriter : createTables, writeModule;
    import std.typecons : tuple;

    auto tables = lexerTables.createTables;
    const moduleName = compilerName ~ "LexerTables";
    const fileName = settings.path(moduleName ~ ".d");

    size_t[] candidates;
    size_t alternativeCount = 0;
    foreach (rule; lexerGrammar.grammar.rules)
        alternativeCount += rule.alternatives.length;
    candidates.length = alternativeCount;
    candidates[] = size_t.max;
    foreach (rule; lexerGrammar.grammar.rules)
    {
        foreach (alternative; rule.alternatives)
        {
            if (auto terminal = alternative in lexerGrammar.candidateTerminals)
                candidates[tables.alternativeIndex(alternative)] = (*terminal).index;
        }
    }

    tables.setLexerMetadata(candidates, lexerGrammar.terminalNames);
    fileName.writeModule(moduleName, tables);
    return tuple!("fileName", "moduleName")(fileName, moduleName);
}

private string[] generateLR1Modules(EAG eag,
    OrderedLR1Tables parserTables, ParserGrammar parserGrammar,
    string bridgeModuleName, string evaluatorModuleName, string lexerTablesModuleName,
    Settings settings)
{
    import gamma.parsgen.lalr1.LR1TablesWriter : createTables, writeModule;
    import io : Input;
    import std.format : format;
    import std.stdio : File;

    const name = eag.BaseName;
    const fileName = settings.path(name ~ ".d");
    const tablesModuleName = name ~ "LRTables";
    const tablesFileName = settings.path(tablesModuleName ~ ".d");
    const tokenMap = format!"[%(%s, %)]"(parserGrammar.terminalToParserToken);
    enum fixName = "lr1gen.fix.d";
    Input fix = Input(fixName, import(fixName));
    File output = File(fileName, "w");

    includeFix(fix, output, '$', fixName);
    output.write(name);
    includeFix(fix, output, '$', fixName);
    output.write(lexerTablesModuleName);
    includeFix(fix, output, '$', fixName);
    output.write(tablesModuleName);
    includeFix(fix, output, '$', fixName);
    output.write(bridgeModuleName);
    includeFix(fix, output, '$', fixName);
    output.write(evaluatorModuleName);
    includeFix(fix, output, '$', fixName);
    output.write(tokenMap);
    includeFix(fix, output, '$', fixName);
    output.close;

    auto tables = parserTables.createTables(parserGrammar.terminals, parserGrammar.nonterminals);

    tablesFileName.writeModule(tablesModuleName, tables);

    return [fileName, tablesFileName];
}

private int[] terminalToParserToken(ParserGrammar parserGrammar)
{
    int[] result;

    foreach (parserTerminal, terminal; parserGrammar.terminals)
    {
        if (terminal.index >= result.length)
        {
            const oldLength = result.length;

            result.length = terminal.index + 1;
            result[oldLength .. $] = -1;
        }
        result[terminal.index] = cast(int) parserTerminal.index;
    }
    return result;
}

private auto generateEpsilonBridgeModule(EAG eag, ParserGrammar parserGrammar,
    Settings settings)
{
    import io : Input;
    import std.stdio : File;
    import std.typecons : tuple;

    const moduleName = eag.BaseName ~ "LREpsilonBridge";
    const fileName = settings.path(moduleName ~ ".d");
    const hyperArity = parserGrammar.hyperArity;
    enum fixName = "lrepsilonbridge.fix.d";
    Input fix = Input(fixName, import(fixName));
    File output = File(fileName, "w");

    includeFix(fix, output, '$', fixName);
    output.write(moduleName);
    includeFix(fix, output, '$', fixName);
    output.write(hyperArity);
    includeFix(fix, output, '$', fixName);
    output.close;

    return tuple!("fileName", "moduleName")(fileName, moduleName);
}

private int hyperArity(ParserGrammar parserGrammar)
{
    int maximumAlternatives = 0;

    foreach (rule; parserGrammar.grammar.rules)
        if (cast(int) rule.alternatives.length > maximumAlternatives)
            maximumAlternatives = cast(int) rule.alternatives.length;

    int result = 1;

    while (result <= maximumAlternatives)
        result *= 2;

    return result;
}

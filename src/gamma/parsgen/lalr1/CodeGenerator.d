module gamma.parsgen.lalr1.CodeGenerator;

import epsilon.eag : EpsilonEAG = EAG;
import epsilon.settings : Settings;
import gamma.input.epsilang.analyzer : EAG;
import gamma.parsgen.lalr1.FixWriter : includeFix;
import gamma.parsgen.lalr1.LexerGrammarBuilder : LexerGrammar;
import gamma.parsgen.lalr1.OrderedLR1Tables;
import gamma.parsgen.lalr1.ParserGrammarBuilder : ParserGrammar;
import gamma.runtime.lr.LR1ParserTables : LexerCandidate, LexerRule;
import std.typecons : Nullable;

public string[] generateCode(EpsilonEAG epsilonEAG, EAG eag,
    OrderedLR1Tables parserTables, ParserGrammar parserGrammar,
    string evaluatorModuleName, string lexerTablesModuleName, Settings settings)
{
    with (generateEpsilonBridgeModule(epsilonEAG, parserGrammar, settings))
        return generateLR1Modules(eag, epsilonEAG.BaseName, parserTables, parserGrammar,
            moduleName, evaluatorModuleName, lexerTablesModuleName, settings)
            ~ fileName;
}

public auto generateLexerCode(OrderedLR1Tables lexerTables, LexerGrammar lexerGrammar,
    string compilerName, Settings settings)
{
    import gamma.parsgen.lalr1.LR1TablesWriter : createTables, writeModule;
    import std.algorithm : map, sum;
    import std.typecons : tuple;

    auto tables = lexerTables.createTables;
    const moduleName = compilerName ~ "LexerTables";
    const fileName = settings.path(moduleName ~ ".d");

    Nullable!LexerCandidate[] candidates;
    LexerRule[] rules;
    const alternativeCount = lexerGrammar.grammar.rules
        .map!(rule => rule.alternatives.length)
        .sum;

    candidates.length = alternativeCount;
    rules.length = alternativeCount;
    foreach (index; 0 .. alternativeCount)
        rules[index] = LexerRule(size_t.max, size_t.max, size_t.max);
    foreach (rule; lexerGrammar.grammar.rules)
    {
        foreach (alternative; rule.alternatives)
        {
            const index = tables.alternativeIndex(alternative);

            if (auto candidate = alternative in lexerGrammar.candidates)
                candidates[index] = *candidate;
            if (auto lexerRule = alternative in lexerGrammar.rules)
                rules[index] = *lexerRule;
        }
    }

    tables.setLexerMetadata(candidates, rules, lexerGrammar.terminalNames, lexerGrammar.nonterminalNames);
    fileName.writeModule(moduleName, tables);

    return tuple!("fileName", "moduleName")(fileName, moduleName);
}

private string[] generateLR1Modules(EAG eag, string name,
    OrderedLR1Tables parserTables, ParserGrammar parserGrammar,
    string bridgeModuleName, string evaluatorModuleName, string lexerTablesModuleName,
    Settings settings)
{
    import gamma.parsgen.lalr1.LR1TablesWriter : createTables, writeModule;
    import io : Input;
    import std.format : format;
    import std.stdio : File;

    const fileName = settings.path(name ~ ".d");
    const tablesModuleName = name ~ "LRTables";
    const tablesFileName = settings.path(tablesModuleName ~ ".d");
    const terminalTokenMap = format!"[%(%s, %)]"(parserGrammar.terminalToParserToken);
    const lexicalTokenMap = format!"[%(%s, %)]"(parserGrammar.lexicalNonterminalToParserToken);
    const sourceTerminals = eag.plainHyperGrammar.terminals.symbolsLiteral;
    const sourceNonterminals = eag.plainHyperGrammar.nonterminals.symbolsLiteral;
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
    output.write(terminalTokenMap);
    includeFix(fix, output, '$', fixName);
    output.write(lexicalTokenMap);
    includeFix(fix, output, '$', fixName);
    output.write(sourceTerminals);
    includeFix(fix, output, '$', fixName);
    output.write(sourceNonterminals);
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

private int[] lexicalNonterminalToParserToken(ParserGrammar parserGrammar)
{
    int[] result = null;

    foreach (parserTerminal, nonterminal; parserGrammar.lexicalTerminals)
    {
        if (nonterminal.index >= result.length)
        {
            const oldLength = result.length;

            result.length = nonterminal.index + 1;
            result[oldLength .. $] = -1;
        }
        result[nonterminal.index] = cast(int) parserTerminal.index;
    }
    return result;
}

private string symbolsLiteral(Symbol)(const Symbol[] symbols)
{
    import std.algorithm : map;
    import std.format : format;

    string symbolLiteral(const Symbol symbol)
    {
        return format!"Symbol(%s, %s)"(symbol.index, stringLiteral(symbol.toString));
    }

    return format!"[%-(%s, %)]"(symbols.map!symbolLiteral);
}

private string stringLiteral(const string text)
{
    import std.string : translate;

    return `"` ~ text.translate(['\\': `\\`, '"': `\"`]) ~ `"`;
}

private auto generateEpsilonBridgeModule(EpsilonEAG epsilonEAG, ParserGrammar parserGrammar,
    Settings settings)
{
    import io : Input;
    import std.stdio : File;
    import std.typecons : tuple;

    const moduleName = epsilonEAG.BaseName ~ "LREpsilonBridge";
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

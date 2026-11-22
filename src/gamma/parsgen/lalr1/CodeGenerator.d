module gamma.parsgen.lalr1.CodeGenerator;

import epsilon.eag : EpsilonEAG = EAG;
import epsilon.settings : Settings;
import gamma.input.epsilang.analyzer : EAG;
import gamma.parsgen.FixWriter : includeFix;
import gamma.parsgen.lalr1.LexerGrammarBuilder : LexerGrammar;
import gamma.parsgen.lalr1.OrderedLR1Tables;
import gamma.parsgen.lalr1.ParserGrammarBuilder : ParserGrammar;
import gamma.runtime.lr.LR1ParserTables : LexerCandidate, LexerRule;
import std.typecons : Nullable;

public string[] generateCode(EpsilonEAG epsilonEAG, EAG eag,
    OrderedLR1Tables parserTables, ParserGrammar parserGrammar,
    string evaluatorModuleName, string lexerTablesModuleName, const string[] terminalNames,
    bool recognizesTokens, Settings settings)
{
    with (generateSyntaxTreeWriterModule(eag, epsilonEAG.BaseName, settings))
        return generateLR1Modules(eag, epsilonEAG.BaseName, parserTables, parserGrammar,
            moduleName, evaluatorModuleName, lexerTablesModuleName, terminalNames,
            recognizesTokens, epsilonEAG.hyperArityMask, settings)
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

    return tuple!("fileName", "moduleName", "terminalNames", "recognizesTokens")(
        fileName, moduleName, lexerGrammar.terminalNames, true);
}

public auto generateEmptyLexerCode(LexerGrammar lexerGrammar, string compilerName,
    Settings settings)
{
    import gamma.parsgen.lalr1.LR1TablesWriter : createEmptyLexerTables, writeModule;
    import std.typecons : tuple;

    const moduleName = compilerName ~ "LexerTables";
    const fileName = settings.path(moduleName ~ ".d");
    auto tables = createEmptyLexerTables;

    tables.setLexerMetadata(null, null, lexerGrammar.terminalNames, lexerGrammar.nonterminalNames);
    fileName.writeModule(moduleName, tables);
    return tuple!("fileName", "moduleName", "terminalNames", "recognizesTokens")(
        fileName, moduleName, lexerGrammar.terminalNames, false);
}

private string[] generateLR1Modules(EAG eag, string name,
    OrderedLR1Tables parserTables, ParserGrammar parserGrammar,
    string syntaxTreeWriterModuleName, string evaluatorModuleName, string lexerTablesModuleName,
    const string[] terminalNames, bool recognizesTokens, int hyperArityMask, Settings settings)
{
    import gamma.parsgen.lalr1.LR1TablesWriter : createTables, writeModule;
    import gamma.parsgen.TerminalRecognizerWriter : writeTerminalRecognizer;
    import io : Input;
    import std.format : format;
    import std.stdio : File;

    const fileName = settings.path(name ~ ".d");
    const tablesModuleName = name ~ "LRTables";
    const tablesFileName = settings.path(tablesModuleName ~ ".d");
    const terminalTokenMap = format!"[%(%s, %)]"(parserGrammar.terminalToParserToken);
    const lexicalTokenMap = format!"[%(%s, %)]"(parserGrammar.lexicalNonterminalToParserToken);
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
    output.write(evaluatorModuleName);
    includeFix(fix, output, '$', fixName);
    output.write(syntaxTreeWriterModuleName);
    includeFix(fix, output, '$', fixName);
    output.write(terminalTokenMap);
    includeFix(fix, output, '$', fixName);
    output.write(lexicalTokenMap);
    includeFix(fix, output, '$', fixName);
    output.write(recognizesTokens);
    includeFix(fix, output, '$', fixName);
    output.writeTerminalRecognizer(terminalNames);
    includeFix(fix, output, '$', fixName);
    output.write(hyperArityMask);
    includeFix(fix, output, '$', fixName);
    output.close;

    auto tables = parserTables.createTables(parserGrammar.terminals, parserGrammar.nonterminals);

    tablesFileName.writeModule(tablesModuleName, tables);

    return [fileName, tablesFileName];
}

private auto generateSyntaxTreeWriterModule(EAG eag, string compilerName, Settings settings)
{
    import io : Input;
    import std.stdio : File;
    import std.typecons : tuple;

    const moduleName = compilerName ~ "SyntaxTreeWriter";
    const fileName = settings.path(moduleName ~ ".d");
    const startWriter = syntaxTreeWriterFunctionName(eag.plainHyperGrammar.startSymbol.index);
    enum fixName = "syntaxtreewriter.fix.d";
    Input fix = Input(fixName, import(fixName));
    File output = File(fileName, "w");

    includeFix(fix, output, '$', fixName);
    output.write(moduleName);
    includeFix(fix, output, '$', fixName);
    output.write(startWriter);
    includeFix(fix, output, '$', fixName);
    output.write(syntaxTreeWriterFunctions(eag));
    includeFix(fix, output, '$', fixName);
    output.close;

    return tuple!("fileName", "moduleName")(fileName, moduleName);
}

private string syntaxTreeWriterFunctions(EAG eag)
{
    import gamma.grammar.Nonterminal : Nonterminal;
    import gamma.grammar.SymbolNode : SymbolNode;
    import gamma.grammar.Terminal : Terminal;
    import std.format : format;
    import std.range : empty;

    string result;

    foreach (rule; eag.plainHyperGrammar.grammar.rules)
    {
        const nonterminal = rule.lhs.nonterminal;
        const writerFunction = syntaxTreeWriterFunctionName(nonterminal.index);

        result ~= "    private size_t " ~ writerFunction
            ~ "(ref Appender!string writer, const long address)\n    {\n"
            ~ "        switch (tree()[address])\n        {\n";
        foreach (alternativeIndex; 0 .. rule.alternatives.length)
        {
            const alternativeWriter = syntaxTreeWriterAlternativeFunctionName(nonterminal.index,
                alternativeIndex + 1);

            result ~= format!"        case %s:\n            return %s(writer, address);\n"(
                alternativeIndex + 1, alternativeWriter);
        }
        result ~= "        default:\n            assert(false, \"unknown syntax-tree alternative\");\n"
            ~ "        }\n    }\n\n";

        foreach (alternativeIndex, alternative; rule.alternatives)
        {
            const alternativeWriter = syntaxTreeWriterAlternativeFunctionName(nonterminal.index,
                alternativeIndex + 1);

            result ~= "    private size_t " ~ alternativeWriter
                ~ "(ref Appender!string writer, const long address)\n    {\n"
                ~ "        const nodeNumber = this.nextNode++;\n"
                ~ `        writer.put(format!"  n%s [label=\"%s\"];\n"(nodeNumber, escape(`
                ~ stringLiteral(nonterminal.toString) ~ ")));\n"
                ~ "        size_t childOffset = 1;\n";

            if (alternative.rhs.empty)
            {
                result ~= "        const childNumber = this.nextNode++;\n"
                    ~ `        writer.put(format!"  n%s [label=\"ε\"];\n"(childNumber));
`
                    ~ `        writer.put(format!"  n%s -> n%s;\n"(nodeNumber, childNumber));
`;
            }

            foreach (node; alternative.rhs)
            {
                auto symbolNode = cast(SymbolNode) node;

                assert(symbolNode !is null);
                result ~= "        {\n";
                if (auto terminal = cast(Terminal) symbolNode.symbol)
                {
                    result ~= "        const childNumber = this.nextNode++;\n"
                        ~ `        writer.put(format!"  n%s [label=\"%s\"];\n"(childNumber, escape(`
                        ~ stringLiteral(terminal.toString) ~ ")));\n"
                        ~ `        writer.put(format!"  n%s -> n%s;\n"(nodeNumber, childNumber));
`;
                }
                else
                {
                    const childNonterminal = cast(Nonterminal) symbolNode.symbol;

                    assert(childNonterminal !is null);
                    result ~= "        const childNumber = "
                        ~ syntaxTreeWriterFunctionName(childNonterminal.index)
                        ~ "(writer, tree()[address + childOffset]);\n"
                        ~ "        ++childOffset;\n"
                        ~ `        writer.put(format!"  n%s -> n%s;\n"(nodeNumber, childNumber));
`;
                }
                result ~= "        }\n";
            }
            result ~= "        return nodeNumber;\n    }\n\n";
        }
    }
    return result;
}

private string syntaxTreeWriterFunctionName(size_t nonterminal)
{
    import std.conv : to;

    return "writeRule" ~ nonterminal.to!string;
}

private string syntaxTreeWriterAlternativeFunctionName(size_t nonterminal, size_t alternative)
{
    import std.conv : to;

    return syntaxTreeWriterFunctionName(nonterminal) ~ "Alternative" ~ alternative.to!string;
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

private string stringLiteral(const string text)
{
    import std.string : translate;

    return `"` ~ text.translate(['\\': `\\`, '"': `\"`]) ~ `"`;
}

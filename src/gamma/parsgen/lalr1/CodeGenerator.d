module gamma.parsgen.lalr1.CodeGenerator;

import epsilon.eag : EAG;
import epsilon.settings : Settings;
import gamma.parsgen.lalr1.OrderedLR1Tables;
import gamma.parsgen.lalr1.ParserGrammarBuilder : ParserGrammar;

public string[] generateCode(EAG eag, OrderedLR1Tables parserTables, ParserGrammar parserGrammar,
    Settings settings)
{
    with (generateEpsilonBridgeModule(eag, parserGrammar, settings))
        return generateLR1Modules(eag, parserTables, parserGrammar,  moduleName, settings) ~ fileName;
}

private string[] generateLR1Modules(EAG eag, OrderedLR1Tables parserTables,
    ParserGrammar parserGrammar, string bridgeModuleName, Settings settings)
{
    import gamma.parsgen.lalr1.LR1ParserTablesWriter : writeTables = write;
    import io : Input;
    import std.format : format;
    import std.stdio : File;

    int[] lexerTokenToParserToken = null;

    lexerTokenToParserToken.length = eag.NextHTerm + 3;
    lexerTokenToParserToken[] = -1;

    foreach (lexerTerminal; EAG.firstHTerm .. eag.NextHTerm)
    {
        const representation = eag.symbolTable.symbol(eag.HTerm[lexerTerminal].Id);

        foreach (parserTerminal; parserTables.grammar.terminals)
            if (parserTerminal.toString == representation)
            {
                lexerTokenToParserToken[lexerTerminal + 3] = cast(int) parserTerminal.index;
                break;
            }
    }

    const name = eag.BaseName;
    const fileName = settings.path(name ~ ".d");
    const tablesModuleName = name ~ "LRTables";
    const tablesFileName = settings.path(tablesModuleName ~ ".d");
    const tokenMap = format!"[%(%s, %)]"(lexerTokenToParserToken);
    enum fixName = "lr1gen.fix.d";
    Input fix = Input(fixName, import(fixName));
    File output = File(fileName, "w");

    void includeFix(char terminator)
    {
        import std.exception : enforce;

        while (fix.front != terminator)
        {
            enforce(fix.front != 0, "unexpected end of lr1gen.fix.d");
            output.write(fix.front);
            fix.popFront;
        }
        fix.popFront;
    }

    includeFix('$');
    output.write(name);
    includeFix('$');
    output.write(name);
    includeFix('$');
    output.write(tablesModuleName);
    includeFix('$');
    output.write(bridgeModuleName);
    includeFix('$');
    output.write(tokenMap);
    includeFix('$');
    output.write(name);
    includeFix('$');
    output.write(name);
    includeFix('$');
    output.write(name);
    includeFix('$');
    output.close;

    tablesFileName.writeTables(tablesModuleName, parserTables, parserGrammar);
    return [fileName, tablesFileName];
}

private auto generateEpsilonBridgeModule(EAG eag, ParserGrammar parserGrammar,
    Settings settings)
{
    import io : Input;
    import std.exception : enforce;
    import std.stdio : File;
    import std.typecons : tuple;

    const moduleName = eag.BaseName ~ "LREpsilonBridge";
    const fileName = settings.path(moduleName ~ ".d");
    const hyperArity = parserGrammar.hyperArity;
    enum fixName = "lrepsilonbridge.fix.d";
    Input fix = Input(fixName, import(fixName));
    File output = File(fileName, "w");

    void includeFix(char terminator)
    {
        while (fix.front != terminator)
        {
            enforce(fix.front != 0, "unexpected end of lrepsilonbridge.fix.d");
            output.write(fix.front);
            fix.popFront;
        }
        fix.popFront;
    }

    includeFix('$');
    output.write(moduleName);
    includeFix('$');
    output.write(hyperArity);
    includeFix('$');
    output.close;
    return tuple!("fileName", "moduleName")(fileName, moduleName);
}

private int hyperArity(ParserGrammar parserGrammar)
{
    int maximumAlternatives;

    foreach (rule; parserGrammar.grammar.rules)
        if (cast(int) rule.alternatives.length > maximumAlternatives)
            maximumAlternatives = cast(int) rule.alternatives.length;

    int result = 1;
    while (result <= maximumAlternatives)
        result *= 2;
    return result;
}

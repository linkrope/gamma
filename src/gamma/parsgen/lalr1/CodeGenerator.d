module gamma.parsgen.lalr1.CodeGenerator;

import epsilon.eag : EAG;
import epsilon.settings : Settings;
import gamma.parsgen.lalr1.OrderedLR1Tables;

public string[] generateCode(EAG eag, OrderedLR1Tables parserTables, Settings settings)
{
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
    output.write(tokenMap);
    includeFix('$');
    output.write(name);
    includeFix('$');
    output.write(name);
    includeFix('$');
    output.write(name);
    includeFix('$');
    output.close;

    import gamma.parsgen.lalr1.LR1ParserTablesWriter : write;

    tablesFileName.write(tablesModuleName, parserTables);
    return [fileName, tablesFileName];
}

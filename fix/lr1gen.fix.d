module $;

import $Lex;
import $;
import gamma.runtime.lr.LR1Parser : LR1Parser;
import gamma.runtime.Lexer : Lexer;
import io : Input, Position, read;
import std.stdio : stdin, writeln;

private enum lexerTokenToParserToken = $;

class GeneratedLexer : Lexer
{
    private int eofToken;

    public this(Input input, int eofToken)
    {
        $Lex.Init(input);
        this.eofToken = eofToken;
    }

    public int nextToken()
    {
        int lexerToken;

        $Lex.Get(lexerToken);
        if (lexerToken == 0)
            return this.eofToken;
        if (lexerToken < 0 || lexerToken >= lexerTokenToParserToken.length)
            return -1;
        return lexerTokenToParserToken[lexerToken];
    }

    public Position position()
    {
        return $Lex.Pos;
    }

}

int main(string[] args)
{
    import core.stdc.stdlib : EXIT_FAILURE;

    Input input = args.length > 1 ? read(args[1]) : read("stdin", stdin);
    auto lexer = new GeneratedLexer(input, cast(int) tables.eofTerminal);
    auto parser = new LR1Parser(tables, lexer);

    parser.parse;
    if (parser.errorCount != 0)
        return EXIT_FAILURE;
    writeln("OK");
    return 0;
}
$

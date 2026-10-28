module $;

import $Lex;
import $;
import $;
import gamma.runtime.lr.LR1Parser : LR1Parser;
import gamma.runtime.Lexer : Lexer;
import io : Input, Position, read;

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
    import gamma.runtime.ParseTreeWriter : ParseTreeWriter;
    import log : Level, levels, trace;
    import std.getopt : getopt;
    import std.stdio : stdin, writeln;

    bool verbose;

    getopt(args, "verbose|v", &verbose);
    if (verbose)
        levels |= Level.trace;

    Input input = args.length > 1 ? read(args[1]) : read("stdin", stdin);
    auto lexer = new GeneratedLexer(input, cast(int) tables.eofTerminal);
    auto parser = new LR1Parser(tables, lexer);
    auto tree = parser.parse;
    auto writer = ParseTreeWriter(tables.terminals, tables.nonterminals);

    trace!"%s"(writer.write(tree));

    if (parser.errorCount == 0)
    {
        auto epsilonTree = transform(tree);

        assert(epsilonTree.tree.length == epsilonTree.positions.length);
        writeln("OK");
    }


    return (parser.errorCount == 0) ? 0 : EXIT_FAILURE;
}
$

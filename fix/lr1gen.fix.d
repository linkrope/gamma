module $;

import $ : lexerTables = tables, candidateTerminals, terminalNames;
import $;
import $;
import Eval = $;
import gamma.runtime.lr.LR1Parser : LR1Parser;
import gamma.runtime.lr.LR1Lexer : LR1Lexer, Token;
import gamma.runtime.Lexer : Lexer;
import io : Input, Position, read;
import log : trace;

private enum terminalToParserToken = $;

class GeneratedLexer : Lexer
{
    private int eofToken;

    private LR1Lexer lrLexer;

    private Position position_;

    public this(Input input, int eofToken)
    {
        this.eofToken = eofToken;
        this.position_ = input.position;
        this.lrLexer = LR1Lexer(input, lexerTables, candidateTerminals);
    }

    public int nextToken()
    {
        if (lrLexer.empty)
            return eofToken;

        const token = lrLexer.front;

        position_ = token.position;
        traceToken(token);
        lrLexer.popFront;

        final switch (token.kind)
        {
        case Token.Kind.terminal:
            if (token.terminal >= terminalToParserToken.length)
                return -1;
            return terminalToParserToken[token.terminal];
        case Token.Kind.end:
            return eofToken;
        case Token.Kind.error:
            return -1;
        }
    }

    public Position position()
    {
        return position_;
    }

    private void traceToken(Token token)
    {
        final switch (token.kind)
        {
        case Token.Kind.terminal:
            trace!"LR lexer terminal %s\n%s"(terminalNames[token.terminal], token.position);
            return;
        case Token.Kind.end:
            trace!"LR lexer end";
            return;
        case Token.Kind.error:
            trace!"LR lexer error\n%s"(token.position);
            return;
        }
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
    bool info;
    bool write;

    getopt(args,
        "info|i", &info,
        "verbose|v", &verbose,
        "write|w", &write,
    );
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
        if (!Eval.EvalInitSucceeds())
            return EXIT_FAILURE;

        auto epsilonTree = transform(tree);

        assert(epsilonTree.tree.length == epsilonTree.positions.length);
        Eval.TraverseSyntaxTree(epsilonTree.tree, epsilonTree.positions, 0, epsilonTree.root,
            epsilonTree.hyperArity, info, write);
        writeln("OK");
    }


    return (parser.errorCount == 0) ? 0 : EXIT_FAILURE;
}
$

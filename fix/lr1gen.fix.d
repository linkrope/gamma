module $;

import $ : lexerTables = tables, lexerCandidates, lexerRules, terminalNames, nonterminalNames;
import $;
import Eval = $;
import $ : SyntaxTreeWriter;
import gamma.runtime.lr.LR1Parser : LR1Parser;
import gamma.runtime.lr.LR1Lexer : LR1Lexer, TerminalCandidate, Token;
import gamma.runtime.lr.SyntaxTreeLexer : SyntaxTreeLexer;
import gamma.runtime.SyntaxTree : SyntaxTreeNode, reset, root, positions, syntaxTreeTerminal = terminal, tree;
import io : Input, Position, read;
import log : error, trace;
import std.sumtype : get;
import std.typecons : Nullable, nullable;

private enum int[] terminalToParserToken = $;
private enum int[] lexicalNonterminalToParserToken = $;
private enum recognizesTokens = $;
$

class GeneratedLexer : SyntaxTreeLexer
{
    private int eofToken;

    private LR1Lexer lrLexer;

    private Position position_;

    private SyntaxTreeNode syntaxTreeNode_;

    public this(Input input, int eofToken)
    {
        this.eofToken = eofToken;
        this.position_ = input.position;
        if (recognizesTokens)
            this.lrLexer = LR1Lexer(input, lexerTables, lexerCandidates, lexerRules,
                input => terminalCandidate(input));
    }

    public int nextToken()
    {
        if (!recognizesTokens)
            return eofToken;

        if (lrLexer.empty)
            return eofToken;

        auto token = lrLexer.front;

        position_ = token.position;
        traceToken(token);
        lrLexer.popFront;

        final switch (token.kind)
        {
        case Token.Kind.terminal:
            syntaxTreeNode_ = syntaxTreeTerminal(position_);
            if (token.terminal >= terminalToParserToken.length)
                return -1;
            return terminalToParserToken[token.terminal];
        case Token.Kind.nonterminal:
            const nonterminal = token.nonterminalIndex;

            syntaxTreeNode_ = SyntaxTreeNode(token.syntaxTreeAddress, position_);
            if (nonterminal >= lexicalNonterminalToParserToken.length)
                return -1;
            return lexicalNonterminalToParserToken[nonterminal];
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

    public SyntaxTreeNode syntaxTreeNode() const
    {
        return syntaxTreeNode_;
    }

    private void traceToken(Token token)
    {
        final switch (token.kind)
        {
        case Token.Kind.terminal:
            trace!"lexer terminal %s\n%s"(terminalNames[token.terminal], token.position);
            return;
        case Token.Kind.nonterminal:
            const nonterminal = token.nonterminalIndex;

            trace!"lexer nonterminal %s\n%s"(nonterminalNames[nonterminal], token.position);
            return;
        case Token.Kind.end:
            trace!"lexer end";
            return;
        case Token.Kind.error:
            error!"%s\n%s"(token.errorMessage.get("unknown token"), token.position);
            return;
        }
    }

}

private size_t nonterminalIndex(Token token)
in (token.kind == Token.Kind.nonterminal)
{
    return token.nonterminal;
}

int main(string[] args)
{
    import core.stdc.stdlib : EXIT_FAILURE;
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
    reset();
    auto lexer = new GeneratedLexer(input, cast(int) tables.eofTerminal);
    auto parser = new LR1Parser(tables, lexer);
    parser.parse;
    auto writer = SyntaxTreeWriter();

    trace!"%s"(writer.write());

    if (parser.errorCount != 0)
        return EXIT_FAILURE;

    if (!Eval.EvalInitSucceeds())
        return EXIT_FAILURE;

    assert(tree().length == positions().length);
    Eval.TraverseSyntaxTree(tree(), positions(), 0, root(), $, info, write);
    writeln("OK");


    return 0;
}
$

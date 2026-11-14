module $;

import $ : lexerTables = tables, lexerCandidates, lexerRules, terminalNames, nonterminalNames;
import $;
import $;
import Eval = $;
import gamma.runtime.lr.LR1Parser : LR1Parser;
import gamma.runtime.lr.LR1Lexer : LR1Lexer, Token;
import gamma.runtime.lr.ParseTreeLexer : ParseTreeLexer;
import gamma.runtime.ParseTree : ParseNode, RuleNode, TerminalNode;
import gamma.runtime.lr.LR1ParserTables : Symbol;
import io : Input, Position, read;
import log : trace;
import std.sumtype : get;

private enum int[] terminalToParserToken = $;
private enum int[] lexicalNonterminalToParserToken = $;
private enum sourceTerminals = $;
private enum sourceNonterminals = $;

class GeneratedLexer : ParseTreeLexer
{
    private int eofToken;

    private LR1Lexer lrLexer;

    private Position position_;

    private const(ParseNode)* parseNode_;

    public this(Input input, int eofToken)
    {
        this.eofToken = eofToken;
        this.position_ = input.position;
        this.lrLexer = LR1Lexer(input, lexerTables, lexerCandidates, lexerRules, terminalNames);
    }

    public int nextToken()
    {
        parseNode_ = null;
        if (lrLexer.empty)
            return eofToken;

        auto token = lrLexer.front;

        position_ = token.position;
        traceToken(token);
        lrLexer.popFront;

        final switch (token.kind)
        {
        case Token.Kind.terminal:
            parseNode_ = new ParseNode(TerminalNode(token.terminal, position_));
            if (token.terminal >= terminalToParserToken.length)
                return -1;
            return terminalToParserToken[token.terminal];
        case Token.Kind.nonterminal:
            const nonterminal = token.nonterminalIndex;

            parseNode_ = token.rule;
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

    public const(ParseNode)* parseNode() const
    in (parseNode_ !is null)
    {
        return parseNode_;
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
            trace!"lexer error\n%s"(token.position);
            return;
        }
    }

}

private size_t nonterminalIndex(Token token)
in (token.kind == Token.Kind.nonterminal)
{
    return (*token.rule).get!(const RuleNode).lhs;
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
    auto writer = ParseTreeWriter(sourceTerminals, sourceNonterminals);

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

module gamma.runtime.lr.LR1Parser_test;

import gamma.runtime.lr.LR1Parser : LR1Parser;
import gamma.runtime.lr.LR1ParserTables : Action, Goto, Halt, LR1ParserTables, Reduce,
    Rule, Shift, Symbol;
import gamma.runtime.lr.SyntaxTreeLexer : SyntaxTreeLexer;
import gamma.runtime.SyntaxTree : reset, SyntaxTreeNode, terminal, tree;
import io : Position;

@("roll back direct syntax-tree construction during LR repair")
unittest
{
    const position = Position("input", 1, 1, "");
    auto lexer = new EndLexer(position);
    auto parser = new LR1Parser(missingTerminalTables, lexer);

    reset;
    parser.parse;

    assert(parser.errorCount == 1);
    assert(tree == [1L]);
}

private immutable LR1ParserTables missingTerminalTables = LR1ParserTables(
    eofTerminal: 1,
    actions: [
    Action(Shift(0, 1, true)),
    Action(Reduce(1, 0, true)),
    Action(Halt(1, true)),
],
    actionOffsets: [0, 1, 2, 3],
    gotos: [Goto(0, 2)],
    gotoOffsets: [0, 1, 1, 1],
    rules: [Rule(0, 1, 1)],
    terminals: [Symbol(0, "'a'"), Symbol(1, "end")],
    nonterminals: [Symbol(0, "S")],
);

private class EndLexer : SyntaxTreeLexer
{
    private Position position_;

    this(const Position position)
    {
        position_ = position;
    }

    public int nextToken()
    {
        return 1;
    }

    public Position position()
    {
        return position_;
    }

    public SyntaxTreeNode syntaxTreeNode() const
    {
        return terminal(position_);
    }
}

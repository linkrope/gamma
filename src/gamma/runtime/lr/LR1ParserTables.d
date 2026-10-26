module gamma.runtime.lr.LR1ParserTables;

import std.sumtype : SumType;

public immutable struct LR1ParserTables
{
    size_t eofTerminal;

    Action[] actions;

    size_t[] actionOffsets;

    Goto[] gotos;

    size_t[] gotoOffsets;

    Rule[] rules;

    string[] terminalRepresentations;

    public size_t terminalCount() const
    {
        return terminalRepresentations.length;
    }
}

public alias Action = SumType!(Shift, Reduce, Halt);

public struct Shift
{
    size_t lookahead;

    size_t state;

    bool isContinuationAction;
}

public struct Reduce
{
    size_t lookahead;

    size_t rule;

    bool isContinuationAction;
}

public struct Halt
{
    size_t lookahead;

    bool isContinuationAction;
}

public struct Goto
{
    size_t nonterminal;

    size_t state;
}

public struct Rule
{
    size_t lhs;

    string lhsName;

    size_t rhsLength;
}

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

    Symbol[] terminals;

    Symbol[] nonterminals;

    public size_t terminalCount() const
    {
        return terminals.length;
    }
}

public struct Symbol
{
    size_t index;

    string name;
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

    size_t rhsLength;

    /// One-based alternative index within the original rules of the LHS.
    size_t alternative;
}

public struct LexerCandidate
{
    public enum Kind { terminal, nonterminal }

    Kind kind;

    size_t symbol = size_t.max;
}

/**
 * Maps a lexer-table reduction back to a source grammar node.
 * Exactly one of `nonterminal` and `terminal` is set for a source reduction.
 */
public struct LexerRule
{
    size_t nonterminal = size_t.max;

    size_t alternative = size_t.max;

    size_t terminal = size_t.max;
}

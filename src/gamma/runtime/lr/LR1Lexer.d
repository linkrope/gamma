module gamma.runtime.lr.LR1Lexer;

import gamma.runtime.lr.LR1ParserTables;
import io : Input, Position;
import std.range : back;
import std.sumtype : match;
import std.uni : isWhite;

public struct Token
{
    public enum Kind { terminal, end, error }

    Kind kind;

    /// Index of the original Gamma terminal, never a compact LR table id.
    size_t terminal = size_t.max;

    Position position;
}

/**
 * A no-repair LR lexer.
 * It recognizes one longest quoted terminal at a time,
 * using (token-end) only as a virtual lookahead:
 * it is never consumed from the source input.
 */
public struct LR1Lexer
{
    private Input input;

    private Token token;

    private immutable LR1ParserTables parserTables;

    private immutable size_t[] candidateTerminals;

    private size_t[string] characterTerminals;

    private Position whiteSpaceErrorPosition;

    public this(Input input, immutable LR1ParserTables parserTables,
        immutable size_t[] candidateTerminals)
    {
        this.input = input;
        this.parserTables = parserTables;
        this.candidateTerminals = candidateTerminals;
        foreach (index, terminal; parserTables.terminals)
            this.characterTerminals[terminal.name] = index;
        readToken;
    }

    public bool empty() const
    {
        return token.kind == Token.Kind.end;
    }

    public Token front() const
    in (!empty)
    {
        return token;
    }

    public void popFront()
    in (!empty)
    {
        readToken;
    }

    private void readToken()
    {
        if (!skipWhiteSpace)
        {
            token = Token(Token.Kind.error, size_t.max, whiteSpaceErrorPosition);
            return;
        }
        if (input.empty)
        {
            token = Token(Token.Kind.end, size_t.max, input.position);
            return;
        }

        const tokenPosition = input.position;
        size_t[] states = [0];
        size_t acceptedTerminal = size_t.max;
        Input remainingInput;

        for (;;)
        {
            const candidate = candidateAtVirtualEnd(states);

            if (candidate != size_t.max)
            {
                acceptedTerminal = candidate;
                remainingInput = input;
            }

            if (input.empty)
                break;

            import std.conv : to;

            const terminal = characterTerminals.get(input.front.to!string, size_t.max);

            if (terminal == size_t.max || !consume(states, terminal))
                break;

            input.popFront;
        }

        if (acceptedTerminal != size_t.max)
        {
            input = remainingInput;
            token = Token(Token.Kind.terminal, acceptedTerminal, tokenPosition);

            return;
        }

        input.popFront;
        token = Token(Token.Kind.error, size_t.max, tokenPosition);
    }

    private dchar next()
    {
        return input.empty ? 0 : input.front;
    }

    private bool skipWhiteSpace()
    {
        for (;;)
        {
            while (!input.empty && input.front.isWhite)
                input.popFront;

            if (input.front != '(')
                return true;

            const commentPosition = input.position;
            Input beforeComment = input;

            input.popFront;

            if (next != '*')
            {
                input = beforeComment;
                return true;
            }
            if (!skipComment(commentPosition))
                return false;
        }
    }

    private bool skipComment(Position commentPosition)
    in (next == '*')
    {
        size_t nesting = 1;
        dchar previous = 0;

        while (!input.empty)
        {
            const character = next;

            input.popFront;

            if (previous == '(' && character == '*')
            {
                ++nesting;
            }
            else if (previous == '*' && character == ')')
            {
                --nesting;
                if (nesting == 0)
                    return true;
            }
            previous = character;
        }

        whiteSpaceErrorPosition = commentPosition;
        return false;
    }

    /**
     * Applies all reductions needed before shifting `terminal`.
     */
    private bool consume(ref size_t[] states, size_t terminal) const
    {
        for (;;)
        {
            Action action;

            if (!actionFor(states.back, terminal, action))
                return false;

            const shifted = action.match!(
                (const Shift shift)
                {
                    states ~= shift.state;
                    return true;
                },
                (const Reduce reduceAction)
                {
                    reduce(states, reduceAction.rule);
                    return false;
                },
                (const Halt halt) => false,
            );

            if (shifted)
                return true;
        }
    }

    /**
     * Parses the virtual end marker against a snapshot.
     */
    private size_t candidateAtVirtualEnd(const size_t[] originalStates) const
    {
        size_t[] states = originalStates.dup;
        size_t candidate = size_t.max;

        for (;;)
        {
            Action action;

            if (!actionFor(states.back, parserTables.eofTerminal, action))
                return size_t.max;

            const completed = action.match!(
                (const Shift shift)
                {
                    states ~= shift.state;
                    return false;
                },
                (const Reduce reduceAction)
                {
                    const sourceTerminal = candidateTerminals[reduceAction.rule];

                    if (sourceTerminal != size_t.max)
                        candidate = sourceTerminal;
                    reduce(states, reduceAction.rule);
                    return false;
                },
                (const Halt halt) => true,
            );

            if (completed)
                return candidate;
        }
    }

    private bool actionFor(size_t state, size_t terminal, out Action result) const
    {
        foreach (action; parserTables.actions[
            parserTables.actionOffsets[state] .. parserTables.actionOffsets[state + 1]])
            if (action.match!(action => action.lookahead) == terminal)
            {
                result = action;
                return true;
            }

        return false;
    }

    private void reduce(ref size_t[] states, size_t ruleIndex) const
    {
        const rule = parserTables.rules[ruleIndex];

        assert(rule.rhsLength < states.length);

        states.length -= rule.rhsLength;

        foreach (goTo; parserTables.gotos[
            parserTables.gotoOffsets[states.back] .. parserTables.gotoOffsets[states.back + 1]])
        {
            if (goTo.nonterminal == rule.lhs)
            {
                states ~= goTo.state;
                return;
            }
        }

        assert(false, "missing lexer goto action");
    }
}

@("skip Unicode WhiteSpace")
unittest
{
    auto result = lexer("\u2003\t");

    assert(result.empty);
}

@("skip nested comments")
unittest
{
    auto result = lexer("(* outer (* inner *) *)  ");

    assert(result.empty);
}

@("skip trailing WhiteSpace")
unittest
{
    auto result = lexer(" \n(* *)\t");

    assert(result.empty);
}

@("recognize an unterminated nested comment")
unittest
{
    import std.string : startsWith;

    auto result = lexer("(* outer (* inner *)");

    assert(result.front.kind == Token.Kind.error);
    assert(result.front.position.toString.startsWith("input:1:1"));
}

version (unittest) private LR1Lexer lexer(string text)
{
    return LR1Lexer(Input("input", text), LR1ParserTables(), candidateTerminals: null);
}

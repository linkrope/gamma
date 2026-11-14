module gamma.runtime.lr.LR1Lexer;

import gamma.runtime.lr.LR1ParserTables;
import gamma.runtime.ParseTree : nodePosition = position, ParseNode, RuleNode, TerminalNode;
import io : Input, Position;
import std.range : back, empty, front;
import std.sumtype : match;
import std.typecons : Nullable, nullable;
import std.uni : isWhite;

public struct Token
{
    public enum Kind { terminal, nonterminal, end, error }

    Kind kind;

    /// Index of the original Gamma terminal, never a compact LR table id.
    size_t terminal = size_t.max;

    Position position;

    const(ParseNode)* rule;
}

/**
 * An LR lexer that recognizes one longest quoted terminal or nonterminal at a time,
 * using (token-end) only as a virtual lookahead: it is never consumed from the source input.
 * It emits one error token for every unrecognized source character.
 */
public struct LR1Lexer
{
    private Input input;

    private Token token;

    private immutable LR1ParserTables parserTables;

    private immutable Nullable!LexerCandidate[] candidates;

    private immutable LexerRule[] rules;

    private immutable string[] terminalNames;

    private size_t[string] characterTerminals;

    private Position whiteSpaceErrorPosition;

    public this(Input input, immutable LR1ParserTables parserTables,
        immutable Nullable!LexerCandidate[] candidates,
        immutable LexerRule[] rules, immutable string[] terminalNames)
    {
        this.input = input;
        this.parserTables = parserTables;
        this.candidates = candidates;
        this.rules = rules;
        this.terminalNames = terminalNames;
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

        const position = input.position;
        size_t[] states = [0];
        ParseNode*[] nodes = null;
        Nullable!Token acceptedToken;
        Input remainingInput;
        const literal = literalCandidate;

        if (!literal.isNull)
        {
            const literalResult = literal.get;

            acceptedToken = Token(Token.Kind.terminal, literalResult.terminal, position).nullable;
            remainingInput = literalResult.remainingInput;
        }

        for (;;)
        {
            auto candidate = candidateAtVirtualEnd(states, nodes, input.position);

            if (!candidate.isNull)
            {
                if (acceptedToken.isNull || input.index > remainingInput.index)
                {
                    acceptedToken = candidate;
                    remainingInput = input;
                }
            }

            if (input.empty)
                break;

            import std.conv : to;

            const terminal = characterTerminals.get(input.front.to!string, size_t.max);

            if (terminal == size_t.max || !consume(states, nodes, terminal, input.position))
                break;

            input.popFront;
        }

        if (!acceptedToken.isNull)
        {
            auto result = acceptedToken.get;

            input = remainingInput;
            result.position = position;
            token = result;

            return;
        }

        input.popFront;
        token = Token(Token.Kind.error, size_t.max, position);
    }

    private dchar next()
    {
        return input.empty ? 0 : input.front;
    }

    private Nullable!LiteralResult literalCandidate() const
    {
        import std.utf : byDchar;

        Nullable!LiteralResult result;

        foreach (terminal, name; terminalNames)
        {
            if (name.empty)
                continue;

            Input cursor = input;
            const representation = name[1 .. $ - 1];

            foreach (character; representation.byDchar)
            {
                if (cursor.empty || cursor.front != character)
                    break;
                cursor.popFront;
            }

            if (cursor.index - input.index != representation.length)
                continue;
            if (result.isNull || cursor.index > result.get.remainingInput.index)
                result = LiteralResult(terminal, cursor);
        }

        return result;
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
    private bool consume(ref size_t[] states, ref ParseNode*[] nodes, size_t terminal,
        const Position position) const
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
                    nodes ~= new ParseNode(TerminalNode(size_t.max, position));
                    return true;
                },
                (const Reduce reduceAction)
                {
                    reduce(states, nodes, reduceAction.rule, position);
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
    private Nullable!Token candidateAtVirtualEnd(const size_t[] originalStates,
        ParseNode*[] originalNodes, const Position position) const
    {
        size_t[] states = originalStates.dup;
        ParseNode*[] nodes = originalNodes.dup;
        Nullable!LexerCandidate matchedCandidate;
        size_t matchedRule = size_t.max;

        for (;;)
        {
            Action action;

            if (!actionFor(states.back, parserTables.eofTerminal, action))
                return Nullable!Token();

            const completed = action.match!(
                (const Shift shift)
                {
                    states ~= shift.state;
                    return false;
                },
                (const Reduce reduceAction)
                {
                    const candidate = candidates[reduceAction.rule];

                    if (!candidate.isNull)
                    {
                        matchedCandidate = candidate;
                        matchedRule = reduceAction.rule;
                        return true;
                    }
                    reduce(states, nodes, reduceAction.rule, position);
                    return false;
                },
                (const Halt halt) => true,
            );

            if (completed)
            {
                if (matchedCandidate.isNull)
                    return Nullable!Token();

                const candidate = matchedCandidate.get;

                if (candidate.kind == LexerCandidate.Kind.terminal)
                    return Token(Token.Kind.terminal, candidate.symbol, position).nullable;

                assert(candidate.kind == LexerCandidate.Kind.nonterminal);

                auto sourceRule = nodes[$ - parserTables.rules[matchedRule].rhsLength];

                assert(sourceRule !is null);

                return Token(Token.Kind.nonterminal, size_t.max, position, sourceRule).nullable;
            }
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

    private void reduce(ref size_t[] states, ref ParseNode*[] nodes,
        size_t ruleIndex, const Position position) const
    {
        const rule = parserTables.rules[ruleIndex];

        assert(rule.rhsLength < states.length);

        states.length -= rule.rhsLength;

        assert(rule.rhsLength <= nodes.length);

        auto children = nodes[$ - rule.rhsLength .. $];

        nodes.length -= rule.rhsLength;

        const source = rules[ruleIndex];

        if (source.terminal != size_t.max)
            nodes ~= new ParseNode(TerminalNode(source.terminal, nodePosition(*children.front)));
        else if (source.nonterminal != size_t.max)
            nodes ~= new ParseNode(RuleNode(source.nonterminal, source.alternative, children,
                children.empty ? position : nodePosition(*children.front)));
        else
            nodes ~= children.length == 1 ? children.front : null;

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

private struct LiteralResult
{
    size_t terminal;

    Input remainingInput;
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
    return LR1Lexer(Input("input", text), LR1ParserTables(), candidates: null, rules: null, terminalNames: null);
}

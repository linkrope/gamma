module gamma.runtime.lr.LR1Lexer;

import gamma.runtime.lr.LR1ParserTables;
import gamma.runtime.SyntaxTree : ruleNode, SyntaxTreeNode, terminalNode;
import io : Input, Position;
import std.range : back, empty, front;
import std.sumtype : match;
import std.typecons : Nullable, nullable;
import std.uni : isWhite;

public struct Token
{
    public enum Kind
    {
        terminal,
        nonterminal,
        end,
        error,
    }

    Kind kind;

    /// Index of the original Gamma terminal, never a compact LR table id.
    size_t terminal = size_t.max;

    Position position;

    size_t nonterminal = size_t.max;

    long syntaxTreeAddress = -1;

    Nullable!string errorMessage;
}

/**
 * The best terminal match beginning at a lexer position.
 */
public struct TerminalCandidate
{
    size_t terminal;

    Input remainingInput;
}

/**
 * Recognizes a terminal from the supplied input position.
 */
public alias TerminalRecognizer = Nullable!TerminalCandidate delegate(Input input);

/**
 * An LR lexer that recognizes one longest terminal or nonterminal at a time,
 * using (token-end) only as a virtual lookahead: it is never consumed from the source input.
 * It emits one error token for every unrecognized source character.
 *
 * Terminals remain separate from lexical nonterminals. A
 * deterministic LR character grammar cannot recognize both a keyword and an
 * extensible identifier with a common prefix: it needs both the shift that
 * completes the keyword and the reduction that lets the identifier continue.
 * Resolving that shift/reduce conflict would lose either terminal
 * priority or longest-match lexical recognition.
 */
public struct LR1Lexer
{
    private Input input;

    private Token token;

    private immutable LR1ParserTables parserTables;

    private immutable Nullable!LexerCandidate[] candidates;

    private immutable LexerRule[] rules;

    private immutable TerminalRecognizer terminalRecognizer;

    private size_t[string] characterTerminals;

    private Position whiteSpaceErrorPosition;

    public this(Input input, immutable LR1ParserTables parserTables,
        immutable Nullable!LexerCandidate[] candidates,
        immutable LexerRule[] rules,
        TerminalRecognizer terminalRecognizer = null)
    {
        this.input = input;
        this.parserTables = parserTables;
        this.candidates = candidates;
        this.rules = rules;
        this.terminalRecognizer = terminalRecognizer;
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
            token = Token(Token.Kind.error, size_t.max, whiteSpaceErrorPosition,
                errorMessage: "comment not closed at end of text".nullable);
            return;
        }
        if (input.empty)
        {
            token = Token(Token.Kind.end, size_t.max, input.position);
            return;
        }

        const position = input.position;
        size_t[] states = [0];
        SyntaxTreeNode[] nodes = null;
        Nullable!Token acceptedToken;
        Input remainingInput = input;
        Nullable!TerminalCandidate literal;

        if (terminalRecognizer !is null)
            literal = terminalRecognizer(input);

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
                if (input.index > remainingInput.index)
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
    private bool consume(ref size_t[] states, ref SyntaxTreeNode[] nodes, size_t terminal,
        const Position position) const
    {
        for (;;)
        {
            Action action;

            if (!actionFor(states.back, terminal, action))
                return false;

            // dfmt off
            const shifted = action.match!(
                (const Shift shift)
                {
                    states ~= shift.state;
                    nodes ~= terminalNode(position);
                    return true;
                },
                (const Reduce reduceAction)
                {
                    reduce(states, nodes, reduceAction.rule, position);
                    return false;
                },
                (const Halt halt) => false,
            );
            // dfmt on

            if (shifted)
                return true;
        }
    }

    /**
     * Parses the virtual end marker against a snapshot.
     */
    private Nullable!Token candidateAtVirtualEnd(const size_t[] originalStates,
        const(SyntaxTreeNode)[] originalNodes, const Position position) const
    {
        size_t[] states = originalStates.dup;
        SyntaxTreeNode[] nodes = originalNodes.dup;
        Nullable!LexerCandidate matchedCandidate;
        size_t matchedRule = size_t.max;

        for (;;)
        {
            Action action;

            if (!actionFor(states.back, parserTables.eofTerminal, action))
                return Nullable!Token();

            // dfmt off
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
            // dfmt on

            if (completed)
            {
                if (matchedCandidate.isNull)
                    return Nullable!Token();

                const candidate = matchedCandidate.get;

                if (candidate.kind == LexerCandidate.Kind.terminal)
                    return Token(Token.Kind.terminal, candidate.symbol, position).nullable;

                assert(candidate.kind == LexerCandidate.Kind.nonterminal);

                auto sourceRule = nodes[$ - parserTables.rules[matchedRule].rhsLength];

                assert(sourceRule.isRule);

                return Token(Token.Kind.nonterminal, size_t.max, position, candidate.symbol,
                    sourceRule.address).nullable;
            }
        }
    }

    private bool actionFor(size_t state, size_t terminal, out Action result) const
    {
        foreach (action; parserTables
            .actions[parserTables.actionOffsets[state] .. parserTables.actionOffsets[state + 1]])
            if (action.match!(action => action.lookahead) == terminal)
            {
                result = action;
                return true;
            }

        return false;
    }

    private void reduce(ref size_t[] states, ref SyntaxTreeNode[] nodes,
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
            nodes ~= children.front;
        else if (source.nonterminal != size_t.max)
            nodes ~= ruleNode(source.alternative, children,
                children.empty ? position : children.front.position);
        else
            nodes ~= children.length == 1 ? children.front : terminalNode(position);

        foreach (goTo; parserTables
            .gotos[parserTables.gotoOffsets[states.back] .. parserTables.gotoOffsets[states.back + 1]])
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
    return LR1Lexer(Input("input", text), LR1ParserTables(), candidates: null, rules: null);
}

module gamma.runtime.lr.LR1Parser;

import gamma.runtime.Lexer;
import gamma.runtime.lr.LR1ParserTables;
import io : Position;
import log;
import std.bitmanip : BitArray;
import std.format;
import std.range;
import std.sumtype : match;

/**
 * An LR(1) parser driven by generated parser tables. It realizes automatic
 * error correction according to J. Röhrich, "Methods for the Automatic
 * Construction of Error Correcting Parsers", Acta Informatica 13 (1980).
 *
 * @author SöKa
 */
public class LR1Parser
{
    private LR1ParserTables parserTables;

    private Lexer lexer;

    private bool haveLookahead;

    private int lookahead;

    private Position lookaheadPosition;

    private size_t state;

    private Stack stack;

    private size_t errorCount_;

    public this(LR1ParserTables parserTables, Lexer lexer)
    {
        this.parserTables = parserTables;
        this.lexer = lexer;
    }

    public size_t errorCount()
    {
        return this.errorCount_;
    }

    public void parse()
    {
        stack.push(0);
        for (;;)
        {
            // Parse normally until a syntax error or halt is detected.
            Action action;

            if (!nextAction(action))
            {
                ++errorCount_;
                error!"Syntax error! Repairing input...\n%s"(lookaheadPosition);
                repairInput;
                continue;
            }

            const halted = action.match!(
                (const Shift shift)
                {
                    trace!"Shift %s"(shift.lookahead);
                    haveLookahead = false;
                    state = shift.state;
                    stack.push(state);
                    trace!"%s"(stack);
                    return false;
                },
                (const Reduce reduceAction)
                {
                    trace!"Reduce %s"(reduceAction.rule);
                    reduce(reduceAction.rule);
                    trace!"%s"(stack);
                    return false;
                },
                (const Halt halt)
                {
                    info!"End of parsing";
                    return true;
                },
            );
            if (halted)
            {
                return;
            }
        }
    }

    private void repairInput()
    {
        // Phase 1: Compute a parse continuation from the parser stack at the
        // syntax error and collect candidate anchor terminals.
        auto stackSnapshot = stack;
        const stateSnapshot = state;
        BitArray anchors;

        anchors.length = parserTables.terminalCount;
        for (;;)
        {
            foreach (action; parserTables.actionsFor(state))
            {
                action.match!(
                    (const Shift shift)
                    {
                        anchors[shift.lookahead] = true;
                    },
                    (const Reduce reduceAction) {},
                    (const Halt halt) {},
                );
            }
            anchors[parserTables.eofTerminal] = true;

            const action = nextContinuationAction;

            const continues = action.match!(
                (const Shift shift)
                {
                    trace!"(C)Shift %s"(shift.lookahead);
                    state = shift.state;
                    stack.push(state);
                    return true;
                },
                (const Reduce reduceAction)
                {
                    trace!"(C)Reduce %s"(reduceAction.rule);
                    reduce(reduceAction.rule);
                    trace!"%s"(stack);
                    return true;
                },
                (const Halt halt)
                {
                    trace!"(C)Halt";
                    return false;
                },
            );
            if (continues)
            {
                continue;
            }
            break;
        }

        // Phase 2: Delete input until an anchor terminal is reached.
        needLookahead;
        while (!anchors[lookahead])
        {
            info!"Deleting %s"(parserTables.terminalRepresentation(lookahead));
            haveLookahead = false;
            needLookahead;
        }

        // Phase 3: Restore the parser state and execute the continuation
        // prefix, inserting terminals until the anchor can be shifted.
        state = stateSnapshot;
        stack = stackSnapshot;
        for (;;)
        {
            if (canShift(lookahead))
                break;

            const action = nextContinuationAction;
            action.match!(
                (const Shift shift)
                {
                    info!"Inserting %s"(parserTables.terminalRepresentation(cast(int) shift.lookahead));
                    state = shift.state;
                    stack.push(state);
                },
                (const Reduce reduceAction)
                {
                    trace!"(I)Reduce %s"(reduceAction.rule);
                    reduce(reduceAction.rule);
                    trace!"%s"(stack);
                },
                (const Halt halt)
                {
                    assert(false, format!"Expecting a shift or reduce action at state %s"(state));
                },
            );
        }

        // The erroneous input has now been repaired.
        info!"Continuing parse in normal mode.";
    }

    private bool nextAction(ref Action result)
    {
        needLookahead;
        foreach (action; parserTables.actionsFor(state))
        {
            if (action.lookahead == lookahead)
            {
                result = action;
                return true;
            }
        }

        return false;
    }

    private bool canShift(int terminal)
    {
        foreach (action; parserTables.actionsFor(state))
        {
            if (action.match!(
                (const Shift shift) => shift.lookahead == terminal,
                _ => false,
            ))
                return true;
        }

        return false;
    }

    private Action nextContinuationAction()
    {
        foreach (action; parserTables.actionsFor(state))
            if (action.isContinuationAction)
                return action;

        assert(false, format!"No continuation action found for state %s"(state));
    }

    private void reduce(size_t ruleIndex)
    {
        const rule = parserTables.rules[ruleIndex];

        stack.pop(rule.rhsLength);
        foreach (goTo; parserTables.gotosFor(stack.top))
        {
            if (goTo.nonterminal == rule.lhs)
            {
                state = goTo.state;
                stack.push(state);
                return;
            }
        }
        throw new Exception("Error in reduce action");
    }

    private void needLookahead()
    {
        if (!haveLookahead)
        {
            haveLookahead = true;
            lookahead = lexer.nextToken;
            lookaheadPosition = lexer.position;
        }
    }

}

private const(Action)[] actionsFor(const LR1ParserTables parserTables, size_t state)
{
    return parserTables.actions[parserTables.actionOffsets[state] .. parserTables.actionOffsets[state + 1]];
}

private const(Goto)[] gotosFor(const LR1ParserTables parserTables, size_t state)
{
    return parserTables.gotos[parserTables.gotoOffsets[state] .. parserTables.gotoOffsets[state + 1]];
}

private size_t lookahead(const Action action)
{
    return action.match!(action => action.lookahead);
}

private bool isContinuationAction(const Action action)
{
    return action.match!(action => action.isContinuationAction);
}

private string terminalRepresentation(const LR1ParserTables parserTables, int terminal)
{
    if (0 <= terminal && terminal < parserTables.terminalRepresentations.length)
        return parserTables.terminalRepresentations[terminal];

    return format!"terminal %s"(terminal);
}

private struct Stack
{
    private size_t[] values;

    this(this)
    {
        values = values.dup;
    }

    void push(size_t value)
    {
        values ~= value;
    }

    size_t top()
    {
        return values.back;
    }

    void pop(size_t count)
    in (count < values.length)
    {
        foreach (i; 0 .. count)
            values.popBack;
    }
}

module gamma.parsgen.lalr1.run.LR1Parser;

import gamma.grammar.Alternative;
import gamma.grammar.Node;
import gamma.grammar.Nonterminal;
import gamma.grammar.SymbolNode;
import gamma.parsgen.lalr1.OrderedLR1Tables;
import gamma.runtime.Scanner;
import log;
import std.algorithm;
import std.bitmanip : BitArray;
import std.format;
import std.range;

private alias Action = OrderedLR1Tables.Action;

/**
 * A *LR(1) parser.
 * Expects "ordered" LR(1) tables to be passed and realizes automatic error correction according to
 * J. Röhrich: "Methods for the Automatic Construction of Error Correcting Parsers",
 *     Acta Informatica 13, 115--139 (1980).
 *
 * @author SöKa
 */
public class LR1Parser
{
    private OrderedLR1Tables parserTables;

    private Scanner scanner;

    private bool haveLookahead;

    private int lookahead;

    private size_t state;

    private ParserStack stack;

    private class ParserStack
    {
        size_t[] stack;

        this()
        {
            // do nothing
        }

        private this(size_t[] stack)
        {
            this.stack = stack.dup;
        }

        void push(size_t x)
        {
            stack ~= x;
        }

        size_t top()
        {
            return stack.back;
        }

        void pop(size_t n)
        in (n >= stack.length)
        {
        	foreach (i; 0 .. n)
            {
				stack.popBack;
			}
        }

        public Object clone()
        {
            return new ParserStack(stack);
        }

        public override string toString()
        {
            import std.format : format;

            return format!"%s"(stack);
        }
    }

    public this(OrderedLR1Tables parserTables, Scanner scanner)
    {
        this.parserTables = parserTables;
        this.scanner = scanner;
        this.haveLookahead = false;
        this.state = 0;
        this.stack = new ParserStack;
    }

    private void needLookadead()
    {
        if (!haveLookahead)
        {
            haveLookahead = true;
            lookahead = scanner.nextToken;
        }
    }

    private Action nextAction()
    {
        Action[] sortedParserActionRow = this.parserTables.getSortedParserActionRow(this.state);

        foreach (action; sortedParserActionRow)
        {
            needLookadead;
            if (action.lookahead.index == this.lookahead)
                return action;
        }
        return null;
    }

    private bool canShift(int terminal)
    {
        Action[] sortedParserActionRow = this.parserTables.getSortedParserActionRow(this.state);

        foreach (action; sortedParserActionRow)
        {
            if (action.lookahead.index == terminal)
                return true;
        }
        return false;
    }

    private Action nextContinuationAction()
    {
        Action[] sortedParserActionRow = this.parserTables.getSortedParserActionRow(this.state);

        foreach (action; sortedParserActionRow)
        {
            if (action.isContinuationAction)
                return action;
        }

        assert(false,
            format!"No continuation action found for state %s"(this.state));
    }

    private void reduce(Alternative alt)
    {
        this.stack.pop(alt.rhs.length);

        OrderedLR1Tables.Goto[] gotoRow = this.parserTables.getSortedGotoRow(this.stack.top);

        foreach (goTo; gotoRow)
        {
            if (goTo.lhs.index == (cast(Nonterminal) alt.lhs.symbol).index)
            {
                this.state = goTo.state;
                this.stack.push(this.state);
                return;
            }
        }
        // TODO: IllegalStateException
        throw new Exception("Error in reduce action");
    }

    private void repairInput()
    {
        // Phase 1: Compute a parse continuation given the parser stack at the moment the syntax error was detected.
        // While computing this, the set of anchor symbol candidates is collected.
        // The current state and stack of the parser is remembered for later
        auto stackSnapshot = cast(ParserStack) this.stack.clone;
        size_t stateSnapshot = this.state;
        BitArray anchors;

        while (true)
        {
            // Collect all terminal-labeled edges in the LR(0) machine departing from state1 as anchor candidates...
            Action[] sortedParserActionRow = this.parserTables.getSortedParserActionRow(this.state);

            if (sortedParserActionRow !is null)
            {
                foreach (action; sortedParserActionRow)
                {
                    if (cast(OrderedLR1Tables.Shift) action)
                        anchors[action.lookahead.index] = true;
                }
            }
            anchors[this.parserTables.eof.index] = true; // eof to the anchors to avoid loop at file end
            // ... and execute the continuation action at this.state.

            Action action = nextContinuationAction;

            assert(action !is null,
                format!"No continuation action at state %s"(this.state));

            if (cast(OrderedLR1Tables.Halt) action)
            {
                trace!"(C)Halt";
                break;
            }
            else if (cast(OrderedLR1Tables.Shift) action)
            {
                OrderedLR1Tables.Shift shiftAction = cast(OrderedLR1Tables.Shift) action;
                trace!"(C)Shift %s"(shiftAction.lookahead);
                this.state = shiftAction.state;
                this.stack.push(this.state);
            }
            else if (cast(OrderedLR1Tables.Reduce) action)
            {
                OrderedLR1Tables.Reduce reduceAction = cast(OrderedLR1Tables.Reduce) action;

                trace!"(C)Reduce %s ::=%-( %s%)"(reduceAction.alternative.lhs.symbol,
                    reduceAction.alternative.rhs.map!(node => (cast(SymbolNode) node).symbol));
                reduce(reduceAction.alternative);
                trace!"%s"(stack);
            }
        }
        // Phase 2: Read ahead in the current input until a terminal symbol from the achors is met.
        // The tokens thus read are deleted from the input in order to repair it.
        needLookadead;
        while (!anchors[this.lookahead])
        {
            info!"Deleting %s"(this.parserTables.grammar.terminal(this.lookahead));
            this.haveLookahead = false;
            needLookadead;
        }
        // Phase 3: Reestablish the initial this.state and this.stack and perform the prefix of the continuation
        // parse of phase 1 until the anchor (head token) of the remaining input can be shifted.
        // Any shift actions executed until the anchor is shifted denote tokens to be inserted.
        this.state = stateSnapshot;
        this.stack = stackSnapshot;
        while (true)
        {
            if (canShift(this.lookahead))
                break;

            Action action = nextContinuationAction;

            assert(action !is null,
                format!"No continuation action at state %s"(this.state));
            assert(cast(OrderedLR1Tables.Halt) action,
                format!"Expecting a shift or reduce action at state %s"(this.state));

            if (cast(OrderedLR1Tables.Shift) action)
            {
                auto shiftAction = cast(OrderedLR1Tables.Shift) action;

                info!"Inserting %s"(shiftAction.lookahead);
                this.state = shiftAction.state;
                this.stack.push(this.state);
            }
            else if (cast(OrderedLR1Tables.Reduce) action)
            {
                auto reduceAction = cast(OrderedLR1Tables.Reduce) action;

                trace!"(I)Reduce %s ::=%-( %s%)"(reduceAction.alternative.lhs.symbol,
                    reduceAction.alternative.rhs.map!(node => (cast(SymbolNode) node).symbol));
                reduce(reduceAction.alternative);
                trace!"%s"(stack);
            }
        }

        // The erroneous input has now been repaired.
        info!"Continuing parse in normal mode.";
    }

    public void parse()
    {
        stack.push(0);
        while (true)
        {
            // The parser is acting normally: it consumes input and does shift and reduce actions
            // until a systax error or halt is detected.
            Action action = nextAction;

            if (action is null)
            {
                info!"line %s, column %s: Syntax error! Repairing input..."(this.scanner.line, this.scanner.column);
                repairInput;
            }
            else if (cast(OrderedLR1Tables.Halt) action)
            {
                info!"End of parsing";
                return;
            }
            else if (cast(OrderedLR1Tables.Shift) action)
            {
                auto shiftAction = cast(OrderedLR1Tables.Shift) action;

                trace!"Shift %s"(shiftAction.lookahead);
                this.haveLookahead = false;
                this.state = shiftAction.state;
                this.stack.push(this.state);
                trace!"%s"(stack);
            }
            else if (cast(OrderedLR1Tables.Reduce) action)
            {
                auto reduceAction = cast(OrderedLR1Tables.Reduce) action;

                trace!"Reduce %s ::=%-( %s%)"(reduceAction.alternative.lhs.symbol,
                    reduceAction.alternative.rhs.map!(node => (cast(SymbolNode) node).symbol));
                reduce(reduceAction.alternative);
                trace!"%s"(stack);
            }
        }
    }

}

module gamma.parsgen.lalr1.CanonicalLR1Tables;

import gamma.grammar.Alternative;
import gamma.grammar.Nonterminal;
import gamma.grammar.Terminal;

/**
 * Abstract view on the parse tables for a deterministic canonical
 * LR-like parser with 1-symbol lookahead. Note that the represented
 * parser may well be a <emph>nondeterministic</emph> one.
 *
 * @author SöKa
 */
public interface CanonicalLR1Tables
{
    public abstract class Action
    {
        public Terminal lookahead;

        public this(Terminal lookahead)
        {
            this.lookahead = lookahead;
        }
    }

    public class Shift : Action
    {
        public int state; // LRMachine.State.index()

        public this(Terminal lookahead, int state)
        {
            super(lookahead);
            this.state = state;
        }
    }

    public class Halt : Action
    {
        public this(Terminal lookahead)
        {
            super(lookahead);
        }
    }

    public class Reduce : Action
    {
        public Alternative alternative;

        public this(Terminal lookahead, Alternative alternative)
        {
            super(lookahead);
            this.alternative = alternative;
        }
    }

    public class Goto
    {
        public Nonterminal lhs;

        public int state; // LRMachine.State.index()

        public this(Nonterminal lhs, int state)
        {
            this.lhs = lhs;
            this.state = state;
        }
    }

    /**
     * Returns the number of states in the parser.
     */
    int stateCount();

    /**
     * Returns the end-of-file Terminal symbol that has been added to
     * the original grammar to generate the parser.
     */
    Terminal eof();

    /**
     * Returns a List of the Shift, Halt, and Reduce entries for the given
     * state's "parser action table" row. Entries are guaranteed to be
     * sorted by the List entries' lookahead.index().
     * <p>
     * Implementation must be such that this method can safely be called
     * multiple times for a fixed <code>state</code> without performance
     * becoming an issue.
     */
    Action[] getSortedParserActionRow(int state);

    /**
     * Returns a List of the Goto entries for the given state's "goto table"
     * row. Entries are guaranteed to be sorted by the List entries'
     * lhs.index().
     * <p>
     * Implementation must be such that this method can safely be called
     * multiple times for a fixed <code>state</code> without performance
     * becoming an issue.
     */
    Goto[] getSortedGotoRow(int state);
}

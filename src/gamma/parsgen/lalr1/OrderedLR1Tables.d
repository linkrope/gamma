module gamma.parsgen.lalr1.OrderedLR1Tables;

import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.Nonterminal;
import gamma.grammar.Terminal;

/**
 * Abstract view on the parse tables for a deterministic ordered LR-like parser
 * with 1-symbol lookahead. The information provided also indicates a continuation
 * automaton for Röhrich's error repair method. Note that the represented parser
 * may well be a <emph>nondeterministic</emph> one.
 *
 * @author SöKa
 */
public interface OrderedLR1Tables
{
    public static abstract class Action
    {
        public bool isContinuationAction;

        public Terminal lookahead;

        public this(Terminal lookahead)
        {
            this.lookahead = lookahead;
            this.isContinuationAction = false;
        }
    }

    public static class Shift : Action
    {
        public size_t state; // LRMachine.State.index

        public this(Terminal lookahead, size_t state)
        {
            super(lookahead);
            this.state = state;
        }
    }

    public static class Halt : Action
    {
        public this(Terminal lookahead)
        {
            super(lookahead);
        }
    }

    public static class Reduce : Action
    {
        public Alternative alternative;

        public this(Terminal lookahead, Alternative alternative)
        {
            super(lookahead);
            this.alternative = alternative;
        }
    }

    public static class Goto
    {
        public Nonterminal lhs;

        public size_t state; // LRMachine.State.index

        public this(Nonterminal lhs, size_t state)
        {
            this.lhs = lhs;
            this.state = state;
        }
    }

    /**
     * Returns the (extended) grammar that underlies the ordered LR tables.
     */
    Grammar grammar();

    /**
     * Returns the number of states in the parser.
     */
    size_t stateCount();

    /**
     * Returns the end-of-file Terminal symbol that has been added to the original
     * grammar to generate the parser.
     */
    Terminal eof();

    /**
     * Returns a List of the Shift, Halt, and Reduce entries for the given state's
     * "parser action table" row. Entries are guaranteed to be sorted by the List
     * entries' lookahead.index().
     * <p>
     * Implementation must be such that this method can safely be called multiple
     * times for a fixed <code>state</code> without performance becoming an issue.
     */
    Action[] getSortedParserActionRow(size_t state);

    /**
     * Returns a List of the Goto entries for the given state's "goto table" row.
     * Entries are guaranteed to be sorted by the List entries's lhs.index().
     * <p>
     * Implementation must be such that this method can safely be called multiple
     * times for a fixed <code>state</code> without performance becoming an issue.
     */
    Goto[] getSortedGotoRow(size_t state);
}

module gamma.parsgen.lalr1.run.OrderedLR1TablesImpl;

import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.SymbolNode;
import gamma.grammar.Terminal;
import gamma.parsgen.lalr1.OrderedLR1Tables;

/**
 * An implementation suitable for use by an LR1 parser.
 *
 * @author SöKa
 */
public class OrderedLR1TablesImpl : OrderedLR1Tables
{
    private size_t stateCount_;

    private Grammar grammar_;

    private Action[][] parserActionRows;

    private Goto[][] gotoRows;

    private Terminal eof_;

    /**
     * Constructor method.
     */
    public this(Grammar grammar, Action[][] parserActionRows, Goto[][] gotoRows)
    in (grammar !is null)
    in (parserActionRows.length == gotoRows.length)
    {
        this.grammar_ = grammar;
        this.parserActionRows = parserActionRows;
        this.gotoRows = gotoRows;
        this.stateCount_ = parserActionRows.length;
        this.eof_ =
            cast(Terminal)(cast(SymbolNode)(cast(Alternative) this
                .grammar_
                .ruleOf(this.grammar_.startSymbol)
                .alternatives[0])
                .rhs[1])
                .symbol;
    }

    /* (non-Javadoc)
     * @see gamma.parsgen.lalr1.OrderedLR1Tables#eof
     */
    public Terminal eof()
    {
        return this.eof_;
    }

    /* (non-Javadoc)
     * @see gamma.parsgen.lalr1.OrderedLR1Tables#getSortedGotoRow(int)
     */
    public Goto[] getSortedGotoRow(size_t state)
    {
        return this.gotoRows[state];
    }

    /* (non-Javadoc)
     * @see gamma.parsgen.lalr1.OrderedLR1Tables#getSortedParserActionRow(int)
     */
    public Action[] getSortedParserActionRow(size_t state)
    {
        return this.parserActionRows[state];
    }

    /* (non-Javadoc)
     * @see gamma.parsgen.lalr1.OrderedLR1Tables#grammar
     */
    public Grammar grammar()
    {
        return this.grammar_;
    }

    /* (non-Javadoc)
     * @see gamma.parsgen.lalr1.OrderedLR1Tables#stateCount
     */
    public size_t stateCount()
    {
        return this.stateCount_;
    }
}

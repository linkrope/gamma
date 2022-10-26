module gamma.grammar.Alternative;

import gamma.grammar.Node;
import gamma.grammar.Nonterminal;
import gamma.grammar.SymbolNode;
import gamma.grammar.Visitor;
import gamma.util.Position;

public class Alternative
{
    private SymbolNode lhs_;

    private Node[] rhs_;

    private Position position_;

    /**
     * Creates an unmodifiable alternative.
     *
     * @param lhs
     *            the nonterminal occurrence for the left-hand side
     * @param rhs
     *            the list of occurrences of symbols or operators for the right-hand side
     * @param position
     *            the position for the alternative
     *
     * @precondition the symbol for the left-hand side is a nonterminal
     */
    public this(SymbolNode lhs, Node[] rhs, Position position)
    in (cast(Nonterminal) lhs.symbol())
    {
        this.lhs_ = lhs;
        this.rhs_ = rhs.dup;
        this.position_ = position;
    }

    public void accept(Visitor visitor)
    {
        visitor.visit(this);
    }

    /**
     * Returns the identifier occurrence for the left-hand side.
     */
    public SymbolNode lhs()
    {
        return this.lhs_;
    }

    /**
     * Returns the list of occurrences of symbols or operators for the right-hand side.
     */
    public Node[] rhs()
    {
        return this.rhs_;
    }

    /**
     * Returns the position for the alternative.
     */
    public Position position()
    {
        return this.position_;
    }
}

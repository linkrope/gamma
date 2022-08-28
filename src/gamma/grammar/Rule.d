module gamma.grammar.Rule;

import gamma.grammar.Alternative;
import gamma.grammar.SymbolNode;
import gamma.grammar.Visitor;
import std.range;

public class Rule
{
    private Alternative[] alternatives_;

    invariant (!alternatives_.empty);

    /**
     * @param alternatives
     *            the non-empty list of alternatives, all with the same nonterminal on the left-hand side
     *
     * @precondition the given list is not empty and all alternatives have the same nonterminal on the left-hand side
     */
    public this(Alternative[] alternatives)
    in (!alternatives.empty)
    {
        auto symbol = alternatives.front.lhs.symbol;

        foreach (alternative; alternatives)
        {
            assert(alternative.lhs.symbol == symbol);
        }
        this.alternatives_ = alternatives.dup;
    }

    public void accept(Visitor visitor)
    {
        visitor.visit(this);
    }

    public SymbolNode lhs()
    {
        return this.alternatives_.front.lhs;
    }

    public Alternative[] alternatives()
    {
        return this.alternatives_;
    }
}

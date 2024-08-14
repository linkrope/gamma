module gamma.grammar.hyper.HyperAlternative;

import gamma.grammar.Alternative;
import gamma.grammar.hyper.Params;
import gamma.grammar.Node;
import gamma.grammar.Nonterminal;
import gamma.grammar.SymbolNode;
import gamma.grammar.hyper.HyperVisitor;
import gamma.util.Position;

public class HyperAlternative : Alternative
{
    alias accept = Alternative.accept;

    private Params params_;

    private Node[] rhs_;

    private Position position_;

    public this(SymbolNode lhs, Params params, Node[] rhs, Position position)
    in (cast(Nonterminal) lhs.symbol())
    {
        super(lhs, rhs, position);
        this.params_ = params;
    }

    public void accept(HyperVisitor visitor)
    {
        visitor.visit(this);
    }

    public Params params()
    {
        return this.params_;
    }
}

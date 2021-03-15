module gamma.grammar.hyper.RepetitionAlternative;

import gamma.grammar.hyper.HyperVisitor;
import gamma.grammar.hyper.Params;
import gamma.grammar.Alternative;
import gamma.grammar.Node;
import gamma.grammar.SymbolNode;
import gamma.grammar.Visitor;
import gamma.util.Position;

public class RepetitionAlternative : Alternative
{
    private Params params_;

    public this(SymbolNode lhs, Node[] rhs, Params params, Position position)
    {
        super(lhs, rhs, position);
        this.params_ = params;
    }

    public override void accept(Visitor visitor)
    {
        (cast(HyperVisitor) visitor).visit(this);
    }

    public Params params()
    {
        return this.params_;
    }
}

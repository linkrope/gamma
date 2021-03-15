module gamma.grammar.hyper.Option;

import gamma.grammar.hyper.HyperVisitor;
import gamma.grammar.hyper.Operator;
import gamma.grammar.hyper.Params;
import gamma.grammar.Rule;
import gamma.util.Position;

public class Option : Operator
{
    alias accept = Operator.accept;

    private Params endParams_;

    public this(Params params, Rule rule, Params endParams, Position position)
    {
        super(params, rule, position);
        this.endParams_ = endParams;
    }

    public override void accept(HyperVisitor visitor) {
        visitor.visit(this);
    }

    public Params endParams()
    {
        return this.endParams;
    }
}

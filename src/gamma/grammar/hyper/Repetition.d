module gamma.grammar.hyper.Repetition;

import gamma.grammar.hyper.HyperVisitor;
import gamma.grammar.hyper.Operator;
import gamma.grammar.hyper.Params;
import gamma.grammar.Rule;
import gamma.util.Position;

public class Repetition : Operator
{
    alias accept = Operator.accept;

    private Params endParams_;

    public this(Rule rule, Params endParams, Position position)
    {
        super(rule, position);
        this.endParams_ = endParams;
    }

    public override void accept(HyperVisitor visitor)
    {
        visitor.visit(this);
    }

    public Params endParams()
    {
        return this.endParams_;
    }
}

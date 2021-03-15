module gamma.grammar.hyper.Group;

import gamma.grammar.hyper.HyperVisitor;
import gamma.grammar.hyper.Operator;
import gamma.grammar.hyper.Params;
import gamma.grammar.Rule;
import gamma.util.Position;

public class Group : Operator
{
    alias accept = Operator.accept;

    public this(Params params, Rule rule, Position position)
    {
        super(params, rule, position);
    }

    public override void accept(HyperVisitor visitor)
    {
        visitor.visit(this);
    }
}

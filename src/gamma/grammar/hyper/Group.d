module gamma.grammar.hyper.Group;

import gamma.grammar.hyper.HyperVisitor;
import gamma.grammar.hyper.Operator;
import gamma.grammar.Rule;
import gamma.util.Position;

public class Group : Operator
{
    alias accept = Operator.accept;

    public this(Rule rule, Position position)
    {
        super(rule, position);
    }

    public override void accept(HyperVisitor visitor)
    {
        visitor.visit(this);
    }
}

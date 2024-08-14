module gamma.grammar.hyper.Operator;

import gamma.grammar.hyper.HyperVisitor;
import gamma.grammar.Node;
import gamma.grammar.Rule;
import gamma.grammar.Visitor;
import gamma.util.Position;

public abstract class Operator : Node
{
    private Rule rule_;

    protected this(Rule rule, Position position)
    {
        super(position);
        this.rule_ = rule;
    }

    public override void accept(Visitor visitor)
    {
        accept(cast(HyperVisitor) visitor);
    }

    public abstract void accept(HyperVisitor visitor);

    public Rule rule()
    {
        return this.rule_;
    }
}

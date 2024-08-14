module gamma.grammar.hyper.ActualParams;

import gamma.grammar.hyper.HyperVisitor;
import gamma.grammar.hyper.Operator;
import gamma.grammar.hyper.Params;
import gamma.grammar.Node;
import gamma.grammar.Visitor;
import gamma.util.Position;

/**
 * This value object represents actual parameters on the right-hand side of a hyper rule.
 *
 * Note that for ident [ ActualParams ] [ ActualParams ] '(' (or '[' or '{')
 * it is not obvious whether single ActualParams belong to ident or to '('.
 * To keep the parser simple, this problem is postponed to semantic analysis.
 */
public class ActualParams : Node
{
    private Params params_;

    public this(Params params)
    {
        super(params.position);
        this.params_ = params;
    }

    public override void accept(Visitor visitor)
    {
        accept(cast(HyperVisitor) visitor);
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

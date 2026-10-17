module gamma.grammar.Alternative;

import gamma.grammar.LhsNode;
import gamma.grammar.Node;
import gamma.grammar.Visitor;
import gamma.util.Position;

public class Alternative
{
    private LhsNode lhs_;

    private Node[] rhs_;

    private Position position_;

    public this(LhsNode lhs, Node[] rhs, Position position)
    {
        this.lhs_ = lhs;
        this.rhs_ = rhs.dup;
        this.position_ = position;
    }

    public void accept(Visitor visitor)
    {
        visitor.visit(this);
    }

    public LhsNode lhs()
    {
        return this.lhs_;
    }

    public Node[] rhs()
    {
        return this.rhs_;
    }

    public Position position()
    {
        return this.position_;
    }
}

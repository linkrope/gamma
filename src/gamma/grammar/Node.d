module gamma.grammar.Node;

import gamma.grammar.Visitor;
import gamma.util.Position;

public abstract class Node
{
    private Position position_;

    protected this(Position position)
    {
        this.position_ = position;
    }

    public abstract void accept(Visitor visitor);

    public Position position()
    {
        return this.position_;
    }
}

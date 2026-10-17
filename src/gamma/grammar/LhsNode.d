module gamma.grammar.LhsNode;

import gamma.grammar.Node;
import gamma.grammar.Nonterminal;
import gamma.grammar.Visitor;
import gamma.util.Position;

public class LhsNode : Node
{
    private Nonterminal nonterminal_;

    public this(Nonterminal nonterminal, Position position)
    {
        super(position);
        this.nonterminal_ = nonterminal;
    }

    public override void accept(Visitor visitor)
    {
        assert(0);
    }

    public Nonterminal nonterminal()
    {
        return this.nonterminal_;
    }
}

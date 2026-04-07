module gamma.grammar.hyper.HyperLhsNode;

import gamma.grammar.affixes.Signature;
import gamma.grammar.hyper.Params;
import gamma.grammar.LhsNode;
import gamma.grammar.Nonterminal;
import gamma.util.Position;

public class HyperLhsNode : LhsNode
{
    private Signature signature_;

    private Params params_;

    public this(Nonterminal nonterminal, Signature signature, Params params, Position position)
    {
        super(nonterminal, position);
        this.params_ = params;
        this.signature_ = signature;
    }

    public Signature signature()
    {
        return this.signature_;
    }

    public Params params()
    {
        return this.params_;
    }
}

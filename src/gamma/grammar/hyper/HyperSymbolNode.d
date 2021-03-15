module gamma.grammar.hyper.HyperSymbolNode;

import gamma.grammar.hyper.Params;
import gamma.grammar.Nonterminal;
import gamma.grammar.SymbolNode;
import gamma.util.Position;

public class HyperSymbolNode : SymbolNode
{
    private Params params_;

    public this(Nonterminal nonterminal, Params params, Position position)
    {
        super(nonterminal, position);
        this.params_ = params;
    }

    public Params params()
    {
        return this.params_;
    }
}

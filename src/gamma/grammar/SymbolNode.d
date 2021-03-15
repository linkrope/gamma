module gamma.grammar.SymbolNode;

import gamma.grammar.Node;
import gamma.grammar.Symbol;
import gamma.grammar.Visitor;
import gamma.util.Position;

public class SymbolNode : Node
{
    private Symbol symbol_;

    public this(Symbol symbol, Position position)
    {
        super(position);
        this.symbol_ = symbol;
    }

    public override void accept(Visitor visitor)
    {
        visitor.visit(this);
    }

    public Symbol symbol()
    {
        return this.symbol_;
    }
}

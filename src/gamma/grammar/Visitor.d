module gamma.grammar.Visitor;

import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.Rule;
import gamma.grammar.SymbolNode;

public interface Visitor
{
    public void visit(Grammar);

    public void visit(Alternative);

    public void visit(SymbolNode);

    public void visit(Rule);
}

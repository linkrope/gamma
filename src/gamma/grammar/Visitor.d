module gamma.grammar.Visitor;

import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.Rule;
import gamma.grammar.SymbolNode;

public interface Visitor
{
	public void visit(Grammar grammar);

	public void visit(Alternative alternative);

	public void visit(SymbolNode symbolNode);

	public void visit(Rule rule);
}

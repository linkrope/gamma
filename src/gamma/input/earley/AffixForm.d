module gamma.input.earley.AffixForm;

import gamma.grammar.SymbolNode;
import gamma.grammar.affixes.Variable;

public class AffixForm
{
    private SymbolNode[] symbolNodes_;

    private Variable[] variables_;

    public this(SymbolNode[] symbolNodes, Variable[] variables)
    {
        this.symbolNodes_ = symbolNodes.dup;
        this.variables_ = variables.dup;
    }

    public bool isSingleVariable() const
    {
        return symbolNodes_.length == 1 && variables_.length == 1;
    }

    public SymbolNode[] symbolNodes()
    {
        return this.symbolNodes_;
    }

    public Variable[] variables()
    {
        return this.variables_;
    }
}

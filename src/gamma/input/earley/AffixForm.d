module gamma.input.earley.AffixForm;

import gamma.grammar.affixes.Variable;
import gamma.grammar.SymbolNode;

/**
 * This immutable value object represents a possible affix form.
 * The sentential form is represented as a sequence of symbol nodes
 * of terminals and nonterminals of a grammar.
 * In addition, for each nonterminal occurrence,
 * the corresponding affix variable is specified.
 */
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

module gamma.grammar.Grammar;

import gamma.grammar.Nonterminal;
import gamma.grammar.Rule;
import gamma.grammar.Terminal;
import gamma.grammar.Visitor;

public class Grammar
{
    private Nonterminal[] nonterminals_;

    private Terminal[] terminals_;

    private Rule[] rules_;

    private Nonterminal startSymbol_;

    private bool isPlain_;

    public this(Nonterminal[] nonterminals, Terminal[] terminals, Rule[] rules, Nonterminal startSymbol)
    {
        import gamma.grammar.SymbolNode : SymbolNode;
        import std.algorithm : all;

        this.nonterminals_ = nonterminals.dup;
        this.terminals_ = terminals.dup;
        this.rules_ = rules.dup;
        this.startSymbol_ = startSymbol;
        this.isPlain_ = this.rules_
            .all!(rule => rule.alternatives
                .all!(alternative => alternative.rhs
                    .all!(node => cast(SymbolNode) node !is null)));
    }

    public void accept(Visitor visitor)
    {
        visitor.visit(this);
    }

    public Nonterminal[] nonterminals()
    {
        return this.nonterminals_;
    }

    public Terminal[] terminals()
    {
        return this.terminals_;
    }

    public Rule[] rules()
    {
        return this.rules_;
    }

    public Nonterminal startSymbol()
    {
        return this.startSymbol_;
    }

    /**
     * Returns whether the grammar is plain.
     * A grammar is said to be plain if it has only terminals or nonterminals
     * (no EBNF expressions) on the right-hand sides of the rules.
     */
    public bool isPlain() const
    {
        return this.isPlain_;
    }

    public Nonterminal nonterminal(size_t index)
    {
        return this.nonterminals_[index];
    }

    public Terminal terminal(size_t index)
    {
        return this.terminals_[index];
    }

    public Rule ruleOf(Nonterminal nonterminal)
    {
        return this.rules_[nonterminal.index];
    }
}

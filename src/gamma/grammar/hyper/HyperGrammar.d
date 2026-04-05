module gamma.grammar.hyper.HyperGrammar;

import gamma.grammar.affixes.Term;
import gamma.grammar.Grammar;

/**
 * Bundles a hyper grammar with its validated affix trees.
 * Affix trees are referenced indirectly via a key stored in each Params.
 */
class HyperGrammar
{
    alias grammar this;

    private Grammar grammar_;

    private Term[][] terms_;

    public this(Grammar grammar, Term[][] terms)
    {
        this.grammar_ = grammar;
        this.terms_ = terms;
    }

    public Grammar grammar()
    {
        return this.grammar_;
    }

    public Term[][] terms()
    {
        return this.terms_;
    }

    public Term[] terms(size_t key)
    in (key < this.terms_.length)
    {
        return this.terms_[key];
    }
}

module gamma.grammar.affixes.Composite;

import gamma.grammar.affixes.Term;
import gamma.grammar.Alternative;

public class Composite : Term
{
    private Alternative alternative_;

    private Term[] terms_;

    public this(Alternative alternative, Term[] terms)
    {
        this.alternative_ = alternative;
        this.terms_ = terms.dup;
    }

    public Alternative alternative()
    {
        return this.alternative_;
    }

    public Term[] terms()
    {
        return this.terms_;
    }
}

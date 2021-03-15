module gamma.grammar.affixes.Variable;

import gamma.grammar.affixes.Term;
import gamma.grammar.Nonterminal;
import gamma.util.Position;

public class Variable : Term
{
    private const bool unequal_;

    private Nonterminal nonterminal_;

    private const int number_;

    private Position position_;

    public this(bool unequal, Nonterminal nonterminal, int number, Position position)
    {
        this.unequal_ = unequal;
        this.nonterminal_ = nonterminal;
        this.number_ = number;
        this.position_ = position;
    }

    public bool unequal() const
    {
        return this.unequal_;
    }

    public Nonterminal nonterminal()
    {
        return this.nonterminal_;
    }

    public int number() const
    {
        return this.number_;
    }

    public Position position()
    {
        return this.position_;
    }
}

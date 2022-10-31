module gamma.grammar.affixes.Variable;

import gamma.grammar.affixes.Term;
import gamma.grammar.Nonterminal;
import gamma.util.Position;
import std.typecons;

/**
 * This immutable value object represents an affix variable.
 * An affix variable is specified by a nonterminal of a grammar.
 * In addition, a number can be given to distinguish the variable from others.
 * Or an annotation that the value must be different from the value
 * of the corresponding variable.
 */
public class Variable : Term
{
    private const bool unequal_;

    private Nonterminal nonterminal_;

    private const Nullable!int number_;

    private Position position_;

    public this(bool unequal, Nonterminal nonterminal, Nullable!int number, Position position)
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

    public Nullable!int number() const
    {
        return this.number_;
    }

    public Position position()
    {
        return this.position_;
    }
}

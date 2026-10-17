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

    private const Nullable!string number_;

    private Position position_;

    public this(bool unequal, Nonterminal nonterminal, Nullable!string number, Position position)
    {
        this.unequal_ = unequal;
        this.nonterminal_ = nonterminal;
        this.number_ = number;
        this.position_ = position;
    }

    public override bool opEquals(Object other) const
    {
        auto that = cast(Variable) other;

        return that !is null && this.unequal_ == that.unequal_ && this.matchesName(that);
    }

    public bool matchesName(const Variable that) const
    {
        return that !is null
            && this.nonterminal_.toString == that.nonterminal_.toString
            && this.number_ == that.number_;
    }

    public override size_t toHash() const
    {
        size_t hash = this.unequal_ ? 1 : 0;

        foreach (c; this.nonterminal_.toString)
            hash = hash * 31 + c;
        hash = hash * 31 + (this.number_.isNull ? 0 : 1);
        if (!this.number_.isNull)
            foreach (c; this.number_.get)
                hash = hash * 31 + c;
        return hash;
    }

    public bool unequal() const
    {
        return this.unequal_;
    }

    public Nonterminal nonterminal()
    {
        return this.nonterminal_;
    }

    public Nullable!string number() const
    {
        return this.number_;
    }

    public Position position()
    {
        return this.position_;
    }

    public override string toString() const
    {
        string result = null;

        if (this.unequal_)
            result ~= "!";
        result ~= this.nonterminal_.toString;
        if (!this.number_.isNull)
            result ~= this.number_.get;

        return result;
    }
}

@("compare variables and their names")
unittest
{
    auto domain = new Nonterminal("n", 0);
    auto otherDomain = new Nonterminal("n", 1);
    auto variable = new Variable(false, domain, "1".nullable, Position.init);
    auto equal = new Variable(false, otherDomain, "1".nullable, Position.init);
    auto unequal = new Variable(true, domain, "1".nullable, Position.init);
    auto differentNumber = new Variable(false, domain, "2".nullable, Position.init);
    auto noNumber = new Variable(false, domain, Nullable!string.init, Position.init);
    auto emptyNumber = new Variable(false, domain, "".nullable, Position.init);

    assert(variable == equal);
    assert(variable.toHash == equal.toHash);
    assert(variable != unequal);
    assert(variable.matchesName(unequal));
    assert(!variable.matchesName(differentNumber));
    assert(variable != differentNumber);
    assert(noNumber != emptyNumber);
}

module gamma.grammar.affixes.Signature;

import gamma.grammar.affixes.Direction;
import gamma.grammar.Nonterminal;
import gamma.util.Position;
import std.range;

public class Signature
{
    private Direction[] directions_;

    private Nonterminal[] domains_;

    private Position position_;

    public this(Direction[] directions, Nonterminal[] domains, Position position)
    in (directions.length == domains.length)
    {
        this.directions_ = directions.dup;
        this.domains_ = domains.dup;
        this.position_ = position;
    }

    public this(Position position)
    {
        this.position_ = position;
    }

    public override bool opEquals(Object other) const
    {
        auto that = cast(Signature) other;

        if (that is null || this.length != that.length)
            return false;
        foreach (index, domain; this.domains_)
            if (domain !is that.domains_[index]
                || this.directions_[index] != that.directions_[index])
                return false;
        return true;
    }

    public override size_t toHash() const
    {
        size_t hash = this.domains_.length;

        foreach (index, domain; this.domains_)
        {
            hash = hash * 31 + (domain is null ? 0 : domain.index);
            hash = hash * 31 + cast(size_t) this.directions_[index];
        }
        return hash;
    }

    public override string toString() const
    {
        import std.format : format;

        string[] items = null;

        foreach (direction, domain; lockstep(this.directions_, this.domains_))
            items ~= format!"%s %s"((direction == Direction.input) ? `-` : `+`, domain);

        return format!"<%-(%s, %)>"(items);
    }

    public size_t length() const
    {
        return this.domains_.length;
    }

    public bool isEmpty() const
    {
        return this.domains_.empty;
    }

    public Direction[] direction()
    {
        return this.directions_;
    }

    public Nonterminal[] domains()
    {
        return this.domains_;
    }

    public Position position()
    {
        return this.position_;
    }
}

module gamma.grammar.hyper.Params;

import gamma.util.Position;

/**
 * Parameter list annotation on a hyper symbol node.
 * The key indexes into external arrays, which holds affix forms first and affix trees after Earley parsing.
 */
public class Params
{
    private const size_t key_;

    private Position position_;

    public this(size_t key, Position position)
    {
        this.key_ = key;
        this.position_ = position;
    }

    public size_t key() const
    {
        return this.key_;
    }

    public Position position()
    {
        return this.position_;
    }
}

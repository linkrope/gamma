module gamma.grammar.Terminal;

import gamma.grammar.Symbol;
import gamma.util.Indexed;

public class Terminal : Symbol, Indexed
{
    private const size_t index_;

    public this(string representation, size_t index)
    {
        super(representation);
        this.index_ = index;
    }

    public override string toString() const
    {
        import std.format : format;
        import std.range : only;

        return format!"%(%s%)"(only(super.toString));
    }

    public size_t index() const
    {
        return this.index_;
    }
}

module gamma.grammar.hyper.AnonymousNonterminal;

import gamma.grammar.Nonterminal;

public class AnonymousNonterminal : Nonterminal
{
    public this(size_t index)
    {
        import std.format : format;

        super(format!"_%s"(index), index);
    }
}

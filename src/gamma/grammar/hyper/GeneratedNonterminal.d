module gamma.grammar.hyper.GeneratedNonterminal;

import gamma.grammar.Nonterminal;

public class GeneratedNonterminal : Nonterminal
{
    /**
     * @param index
     *            the index of the generated nonterminal
     */
    public this(size_t index)
    {
        import std.format : format;

        super(format!"YYNont%s"(index), index);
    }
}

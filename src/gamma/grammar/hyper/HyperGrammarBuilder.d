module gamma.grammar.hyper.HyperGrammarBuilder;

import gamma.grammar.GrammarBuilder;
import gamma.grammar.hyper.AnonymousNonterminal;
import gamma.grammar.Nonterminal;

public struct HyperGrammarBuilder
{
    GrammarBuilder builder;

    alias builder this;

    public AnonymousNonterminal buildAnonymousNonterminal()
    {
        import std.exception : enforce;
        import std.format : format;

        const index = builder.nonterminals.length;
        auto nonterminal = new AnonymousNonterminal(index);

        enforce(nonterminal.toString !in builder.nonterminalMap,
                format!"generated nonterminal name already defined by the user: %s"(nonterminal));

        builder.nonterminalMap[nonterminal.toString] = nonterminal;
        builder.nonterminals ~= nonterminal;
        builder.alternativesMap ~= null;

        return nonterminal;
    }
}

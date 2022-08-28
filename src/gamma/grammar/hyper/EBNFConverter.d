module gamma.grammar.hyper.EBNFConverter;

import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.hyper.Group;
import gamma.grammar.hyper.HyperVisitor;
import gamma.grammar.hyper.Option;
import gamma.grammar.hyper.Repetition;
import gamma.grammar.hyper.RepetitionAlternative;
import gamma.grammar.Nonterminal;
import gamma.grammar.Rule;
import gamma.grammar.SymbolNode;
import gamma.grammar.Terminal;
import std.algorithm : each;

public Grammar convert(Grammar grammar)
in (grammar !is null)
{
    auto visitor = new EBNFConverter;

    visitor.visit(grammar);
    return visitor.grammar;
}

private class EBNFConverter : HyperVisitor
{
    Nonterminal[] nonterminals;

    Terminal[] terminals;

    Alternative[] alternatives;

    Nonterminal startSymbol;

    void visit(Grammar grammar)
    {
        this.nonterminals = grammar.nonterminals;
        this.terminals = grammar.terminals;
        this.alternatives = null;
        this.startSymbol = grammar.startSymbol;
        grammar.rules.each!(rule => rule.accept(this));
    }

    void visit(Alternative alternative)
    {
        // TODO
        this.alternatives ~= alternative;
        alternative.rhs.each!(node => node.accept(this));
    }

    void visit(SymbolNode symbolNode)
    {
        // TODO
    }

    void visit(Rule rule)
    {
        // TODO
        rule.alternatives.each!(alternative => alternative.accept(this));
    }

    void visit(Group group)
    {
        // TODO
    }

    void visit(Option option)
    {
        // TODO
    }

    void visit(Repetition repetition)
    {
        // TODO
    }

    void visit(RepetitionAlternative alternative)
    {
        // TODO
    }

    Grammar grammar()
    {
        import std.algorithm : filter;
        import std.array : array;
        import log;

        Rule[] rules;

        foreach (nonterminal; this.nonterminals)
        {
            auto alternatives = this.alternatives
                .filter!(alternative => alternative.lhs.symbol == nonterminal);

            if (!alternatives.empty)
                rules ~= new Rule(alternatives.array);
        }
        return new Grammar(this.nonterminals, this.terminals, rules, this.startSymbol);
    }
}

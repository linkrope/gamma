module gamma.grammar.hyper.EBNFConverter;

import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.hyper.ActualParams;
import gamma.grammar.hyper.Group;
import gamma.grammar.hyper.HyperAlternative;
import gamma.grammar.hyper.HyperVisitor;
import gamma.grammar.hyper.Option;
import gamma.grammar.hyper.Repetition;
import gamma.grammar.Node;
import gamma.grammar.Nonterminal;
import gamma.grammar.Rule;
import gamma.grammar.SymbolNode;
import gamma.grammar.Terminal;
import std.algorithm : each;
import std.range;

public Grammar convert(Grammar grammar)
in (grammar !is null)
out (convertedGrammar; convertedGrammar.isPlain)
{
    auto visitor = new EBNFConverter;

    visitor.visit(grammar);
    return visitor.grammar;
}

// TODO: check position for additional empty alternatives and right recursion
private class EBNFConverter : HyperVisitor
{
    Nonterminal[] nonterminals;

    Terminal[] terminals;

    Alternative[] alternatives;

    Nonterminal startSymbol;

    bool[] repetitionStack;

    Node[][] rhsStack;

    void visit(Grammar grammar)
    in (grammar !is null)
    {
        this.nonterminals = grammar.nonterminals;
        this.terminals = grammar.terminals;
        this.alternatives = null;
        this.startSymbol = grammar.startSymbol;

        this.repetitionStack ~= false;
        scope (exit)
            this.repetitionStack.popBack;

        grammar.rules.each!(rule => rule.accept(this));
    }

    void visit(HyperAlternative hyperAlternative)
    {
        visit(cast(Alternative) hyperAlternative);
    }

    void visit(Alternative alternative)
    {
        this.rhsStack ~= null;
        scope (exit)
            this.rhsStack.popBack;

        alternative.rhs.each!(node => node.accept(this));
        if (this.repetitionStack.back)
            this.rhsStack.back ~= alternative.lhs;
        this.alternatives ~= new Alternative(alternative.lhs, this.rhsStack.back, alternative.position);
    }

    void visit(SymbolNode symbolNode)
    {
        this.rhsStack.back ~= symbolNode;
    }

    void visit(ActualParams)
    {
        // do nothing
    }

    void visit(Rule rule)
    {
        rule.alternatives.each!(alternative => alternative.accept(this));
    }

    void visit(Group group)
    {
        this.repetitionStack ~= false;
        scope (exit)
            this.repetitionStack.popBack;

        this.rhsStack.back ~= group.rule.lhs;
        group.rule.accept(this);
    }

    void visit(Option option)
    {
        this.repetitionStack ~= false;
        scope (exit)
            this.repetitionStack.popBack;

        this.rhsStack.back ~= option.rule.lhs;
        option.rule.accept(this);

        auto nonterminal = cast(Nonterminal) option.rule.lhs.symbol;
        auto symbolNode = new SymbolNode(nonterminal, option.position);

        this.alternatives ~= new Alternative(symbolNode, null, option.position);
    }

    void visit(Repetition repetition)
    {
        this.repetitionStack ~= true;
        scope (exit)
            this.repetitionStack.popBack;

        this.rhsStack.back ~= repetition.rule.lhs;
        repetition.rule.accept(this);

        auto nonterminal = cast(Nonterminal) repetition.rule.lhs.symbol;
        auto symbolNode = new SymbolNode(nonterminal, repetition.position);

        this.alternatives ~= new Alternative(symbolNode, null, repetition.position);
    }

    Grammar grammar()
    {
        import std.algorithm : filter;
        import std.array : array;

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

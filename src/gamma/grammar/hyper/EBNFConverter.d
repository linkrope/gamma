module gamma.grammar.hyper.EBNFConverter;

import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.hyper.Group;
import gamma.grammar.hyper.HyperSymbolNode;
import gamma.grammar.hyper.HyperVisitor;
import gamma.grammar.hyper.Option;
import gamma.grammar.hyper.Repetition;
import gamma.grammar.hyper.RepetitionAlternative;
import gamma.grammar.Node;
import gamma.grammar.Nonterminal;
import gamma.grammar.Rule;
import gamma.grammar.SymbolNode;
import gamma.grammar.Terminal;
import std.algorithm : each;
import std.range;

public Grammar convert(Grammar grammar)
in (grammar !is null)
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

    SymbolNode[] lhsStack;

    Node[][] rhsStack;

    void visit(Grammar grammar)
    in (grammar !is null)
    {
        this.nonterminals = grammar.nonterminals;
        this.terminals = grammar.terminals;
        this.alternatives = null;
        this.startSymbol = grammar.startSymbol;
        grammar.rules.each!(rule => rule.accept(this));
    }

    void visit(Alternative alternative)
    {
        this.rhsStack ~= null;
        alternative.rhs.each!(node => node.accept(this));
        this.alternatives ~= new Alternative(alternative.lhs, this.rhsStack.back, alternative.position);
        this.rhsStack.popBack;
    }

    void visit(SymbolNode symbolNode)
    {
        this.rhsStack.back ~= symbolNode;
    }

    void visit(Rule rule)
    {
        this.lhsStack ~= rule.lhs;
        rule.alternatives.each!(alternative => alternative.accept(this));
        this.lhsStack.popBack;
    }

    void visit(Group group)
    {
        this.rhsStack.back ~= group.rule.lhs;
        group.rule.accept(this);
    }

    void visit(Option option)
    {
        this.rhsStack.back ~= option.rule.lhs;
        option.rule.accept(this);

        auto nonterminal = cast(Nonterminal) option.rule.lhs.symbol;
        SymbolNode symbolNode = new HyperSymbolNode(nonterminal, option.endParams, option.position);

        this.alternatives ~= new Alternative(symbolNode, null, option.position);
    }

    void visit(Repetition repetition)
    {
        this.rhsStack.back ~= repetition.rule.lhs;
        repetition.rule.accept(this);

        auto nonterminal = cast(Nonterminal) repetition.rule.lhs.symbol;
        SymbolNode symbolNode = new HyperSymbolNode(nonterminal, repetition.endParams, repetition.position);

        this.alternatives ~= new Alternative(symbolNode, null, repetition.position);
    }

    void visit(RepetitionAlternative alternative)
    {
        this.rhsStack ~= null;
        alternative.rhs.each!(node => node.accept(this));

        auto nonterminal = cast(Nonterminal) this.lhsStack.back.symbol;
        SymbolNode symbolNode = new HyperSymbolNode(nonterminal, alternative.params, alternative.position);
        Node[] rhs = this.rhsStack.back ~ symbolNode;

        this.alternatives ~= new Alternative(alternative.lhs, rhs, alternative.position);
        this.rhsStack.popBack;
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

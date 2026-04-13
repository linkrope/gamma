module gamma.grammar.hyper.EBNFConverter;

import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.hyper.Group;
import gamma.grammar.hyper.HyperLhsNode;
import gamma.grammar.hyper.HyperSymbolNode;
import gamma.grammar.hyper.HyperVisitor;
import gamma.grammar.hyper.Operator;
import gamma.grammar.hyper.Option;
import gamma.grammar.hyper.Repetition;
import gamma.grammar.hyper.RepetitionAlternative;
import gamma.grammar.LhsNode;
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

    LhsNode[] lhsStack;

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
        if (!alternative.isInlinedOperator)
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
        auto nonterminal = group.rule.lhs.nonterminal;

        this.rhsStack.back ~= new HyperSymbolNode(nonterminal, group.params, group.position);
        group.rule.accept(this);
    }

    void visit(Option option)
    {
        auto nonterminal = option.rule.lhs.nonterminal;

        this.rhsStack.back ~= new HyperSymbolNode(nonterminal, option.params, option.position);
        option.rule.accept(this);

        auto signature = (cast(HyperLhsNode) option.rule.alternatives.front.lhs).signature;
        auto lhsNode = new HyperLhsNode(nonterminal, signature, option.endParams, option.position);

        this.alternatives ~= new Alternative(lhsNode, null, option.position);
    }

    void visit(Repetition repetition)
    {
        auto nonterminal = repetition.rule.lhs.nonterminal;

        this.rhsStack.back ~= new HyperSymbolNode(nonterminal, repetition.params, repetition.position);
        repetition.rule.accept(this);

        auto signature = (cast(HyperLhsNode) repetition.rule.alternatives.front.lhs).signature;
        auto lhsNode = new HyperLhsNode(nonterminal, signature, repetition.endParams, repetition.position);

        this.alternatives ~= new Alternative(lhsNode, null, repetition.position);
    }

    void visit(RepetitionAlternative alternative)
    {
        this.rhsStack ~= null;
        alternative.rhs.each!(node => node.accept(this));

        auto nonterminal = this.lhsStack.back.nonterminal;
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
                .filter!(alternative => alternative.lhs.nonterminal == nonterminal);

            if (!alternatives.empty)
                rules ~= new Rule(alternatives.array);
        }

        return new Grammar(this.nonterminals, this.terminals, rules, this.startSymbol);
    }
}

private bool isInlinedOperator(Alternative alternative)
{
    if (alternative.rhs.length != 1)
        return false;

    auto operator = cast(Operator) alternative.rhs.front;

    return operator !is null && operator.rule.lhs.nonterminal == alternative.lhs.nonterminal;
}

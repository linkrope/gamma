module gamma.grammar.hyper.HyperGrammarBuilder;

import gamma.grammar.affixes.Signature;
import gamma.grammar.Alternative;
import gamma.grammar.GrammarBuilder;
import gamma.grammar.hyper.AnonymousNonterminal;
import gamma.grammar.hyper.Group;
import gamma.grammar.hyper.HyperLhsNode;
import gamma.grammar.hyper.Operator;
import gamma.grammar.hyper.Option;
import gamma.grammar.hyper.Repetition;
import gamma.grammar.Node;
import gamma.grammar.Nonterminal;
import gamma.grammar.Rule;
import std.range;

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

    /**
     * Replaces each anonymous nonterminal whose EBNF operator appears exclusively on the RHS
     * of a single alternative with the nonterminal from the LHS.
     *
     * Returns: a map of nonterminal → signature for each nonterminal that was inlined
     * and whose operator carried formal parameters.
     */
    public Signature[Nonterminal] inlineSingleOperators()
    {
        import std.algorithm : map;
        import std.array : array;

        Signature[Nonterminal] signatureByNonterminal;

        foreach (nonterminal; builder.nonterminals)
        {
            if (cast(AnonymousNonterminal) nonterminal)
                continue;

            auto alternatives = builder.alternativesMap[nonterminal.index];

            if (alternatives.length != 1)
                continue;

            auto alternative = alternatives.front;

            if (alternative.rhs.length != 1)
                continue;

            auto operator = cast(Operator) alternative.rhs.front;

            if (operator is null)
                continue;

            auto alternativeLhs = cast(HyperLhsNode) alternative.lhs;

            if (alternativeLhs !is null && alternativeLhs.params !is null)
                continue;

            auto rule = new Rule(operator.rule.alternatives.map!(a => a.rebuild(nonterminal)).array);
            Node rebuiltOperator = rebuildOperator(operator, rule);
            auto rebuiltAlternative = new Alternative(alternative.lhs, [rebuiltOperator], alternative.position);

            builder.alternativesMap[nonterminal.index][0] = rebuiltAlternative;

            if (auto lhsNode = cast(HyperLhsNode) rule.lhs)
                if (lhsNode.signature !is null)
                    signatureByNonterminal[nonterminal] = lhsNode.signature;
        }
        return signatureByNonterminal;
    }
}

private Operator rebuildOperator(Operator operator, Rule rule)
{
    if (auto group = cast(Group) operator)
        return new Group(group.params, rule, group.position);
    if (auto option = cast(Option) operator)
        return new Option(option.params, rule, option.endParams, option.position);
    if (auto repetition = cast(Repetition) operator)
        return new Repetition(repetition.params, rule, repetition.endParams, repetition.position);

    assert(false, "unknown operator type");
}

private Alternative rebuild(Alternative alternative, Nonterminal nonterminal)
{
    import gamma.grammar.hyper.RepetitionAlternative : RepetitionAlternative;

    auto alternativeLhs = cast(HyperLhsNode) alternative.lhs;
    auto lhs = new HyperLhsNode(nonterminal, alternativeLhs.signature, alternativeLhs.params, alternativeLhs.position);

    if (auto repetitionAlt = cast(RepetitionAlternative) alternative)
        return new RepetitionAlternative(lhs, alternative.rhs, repetitionAlt.params, alternative.position);
    return new Alternative(lhs, alternative.rhs, alternative.position);
}

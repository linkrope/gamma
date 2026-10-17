module gamma.grammar.hyper.Operator;

import gamma.grammar.hyper.HyperVisitor;
import gamma.grammar.hyper.Params;
import gamma.grammar.Node;
import gamma.grammar.Rule;
import gamma.grammar.Visitor;
import gamma.util.Position;

public abstract class Operator : Node
{
    private Params params_;

    private Rule rule_;

    protected this(Params params, Rule rule, Position position)
    {
        super(position);
        this.params_ = params;
        this.rule_ = rule;
    }

    public override void accept(Visitor visitor)
    {
        accept(cast(HyperVisitor) visitor);
    }

    public abstract void accept(HyperVisitor visitor);

    public Params params()
    {
        return this.params_;
    }

    public Rule rule()
    {
        return this.rule_;
    }
}

/**
 * Returns the sole operator of an unparameterized rule, if any.
 */
public Operator directOperator(Rule rule)
{
    import gamma.grammar.hyper.HyperLhsNode : HyperLhsNode;
    import std.range : front;

    if (rule.alternatives.length != 1)
        return null;

    auto alternative = rule.alternatives.front;
    auto lhs = cast(HyperLhsNode) alternative.lhs;

    if (lhs is null || lhs.params !is null || alternative.rhs.length != 1)
        return null;

    auto operator = cast(Operator) alternative.rhs.front;

    if (operator is null || operator.params !is null)
        return null;

    return operator;
}

/**
 * Returns a direct anonymous operator belonging to a named rule, if any.
 */
public Operator directNamedOperator(Rule rule)
{
    import gamma.grammar.hyper.AnonymousNonterminal : AnonymousNonterminal;

    if (cast(AnonymousNonterminal) rule.lhs.nonterminal)
        return null;

    auto operator = rule.directOperator;

    if (operator is null || !cast(AnonymousNonterminal) operator.rule.lhs.nonterminal)
        return null;

    return operator;
}

@("distinguish direct operators of named and anonymous rules")
unittest
{
    import gamma.grammar.Alternative : Alternative;
    import gamma.grammar.hyper.AnonymousNonterminal : AnonymousNonterminal;
    import gamma.grammar.hyper.Group : Group;
    import gamma.grammar.hyper.HyperLhsNode : HyperLhsNode;
    import gamma.grammar.Nonterminal : Nonterminal;

    Rule makeRule(Nonterminal nonterminal, Node[] rhs)
    {
        auto lhs = new HyperLhsNode(nonterminal, null, null, Position.init);

        return new Rule([new Alternative(lhs, rhs, Position.init)]);
    }

    auto inner = new AnonymousNonterminal(1);
    auto group = new Group(null, makeRule(inner, null), Position.init);
    // S: ( ).
    auto named = makeRule(new Nonterminal("S", 0), [group]);
    // S: ( ( ) ).
    auto anonymous = makeRule(new AnonymousNonterminal(2), [group]);

    assert(named.directOperator is group);
    assert(named.directNamedOperator is group);
    assert(anonymous.directOperator is group);
    assert(anonymous.directNamedOperator is null);
}

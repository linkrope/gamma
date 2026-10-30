module $;

import gamma.runtime.ParseTree;
import io : Position;
import std.sumtype : match;

public struct EpsilonSyntaxTree
{
    long[] tree;
    Position[] positions;
    long root;
    int hyperArity;
}

public EpsilonSyntaxTree transform(const ParseTree parseTree)
{
    EpsilonSyntaxTree result;

    result.root = encodeNode(parseTree.root, result);
    result.hyperArity = $;
    return result;
}

private long encodeNode(const(ParseNode)* node, ref EpsilonSyntaxTree result)
in (node !is null)
{
    return (*node).match!(
        (const TerminalNode terminal)
        {
            throw new Exception("a serialized parse tree root must be a rule");
            return 0;
        },
        (const RuleNode rule)
        {
            const address = result.tree.length;
            const length = address + 1 + ruleChildCount(rule);

            result.tree.length = length;
            result.positions.length = length;
            result.tree[address] = cast(long) rule.alternative;
            result.positions[address] = rule.position;

            size_t offset = 1;
            foreach (child; rule.children)
            {
                (*child).match!(
                    (const TerminalNode terminal) {},
                    (const RuleNode childRule)
                    {
                        const childAddress = encodeNode(child, result);

                        result.tree[address + offset] = childAddress;
                        result.positions[address + offset] = childRule.position;
                        ++offset;
                    },
                );
            }
            return cast(long) address;
        },
    );
}

private size_t ruleChildCount(const RuleNode rule)
{
    import std.algorithm : map, sum;

    return rule.children
        .map!(child => (*child).match!(
            (const TerminalNode terminal) => cast(size_t) 0,
            (const RuleNode childRule) => cast(size_t) 1,
        ))
        .sum;
}
$

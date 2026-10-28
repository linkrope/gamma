module gamma.runtime.ParseTree;

import io : Position;
import std.sumtype;

public struct ParseTree
{
    const(ParseNode)* root;

    const Position endPosition;

    public this(ParseNode* root, const Position endPosition)
    in (root !is null)
    {
        this.root = root;
        this.endPosition = endPosition;
    }
}

public alias ParseNode = SumType!(TerminalNode, RuleNode);

/**
 * A terminal occurrence in the parse.
 */
public struct TerminalNode
{
    const size_t terminal;

    const Position position;

    public this(size_t terminal, const Position position)
    {
        this.terminal = terminal;
        this.position = position;
    }
}

/**
 * A grammar-rule application, with LHS index and children in RHS order.
 */
public struct RuleNode
{
    const size_t lhs;

    const(ParseNode*[]) children;

    const Position position;

    public this(size_t lhs, const ParseNode*[] children, const Position position)
    {
        this.lhs = lhs;
        this.children = children.dup;
        this.position = position;
    }
}

public const(Position) position(const ParseNode node)
{
    return node.match!(
        (const TerminalNode terminal) => terminal.position,
        (const RuleNode rule) => rule.position,
    );
}

module gamma.runtime.ParseTree;

import io : Position;
import std.sumtype;

public struct ParseTree
{
    const(ParseNode)* root;

    const Position endPosition;

    public this(ParseNode* root, Position endPosition)
    in (root !is null)
    {
        this.root = root;
        this.endPosition = endPosition;
    }
}

public alias ParseNode = SumType!(Terminal, Rule);

/**
 * A terminal occurrence in the parse.
 */
public struct Terminal
{
    const size_t terminal;

    const Position position;

    public this(size_t terminal, Position position)
    {
        this.terminal = terminal;
        this.position = position;
    }
}

/**
 * A grammar-rule application, with children in RHS order.
 */
public struct Rule
{
    const size_t ruleAlt;

    const(ParseNode*[]) children;

    const Position position;

    public this(size_t ruleAlt, ParseNode*[] children, Position position)
    {
        this.ruleAlt = ruleAlt;
        this.children = children.dup;
        this.position = position;
    }
}

public const(Position) position(const ParseNode node)
{
    return node.match!(
        (const Terminal terminal) => terminal.position,
        (const Rule rule) => rule.position,
    );
}

module gamma.runtime.SyntaxTree;

import io : Position;

/**
 * The evaluator-compatible syntax tree shared by an LR lexer and parser.
 *
 * A rule record begins with its one-based alternative, followed by the
 * addresses of its nonterminal children. Terminal occurrences have no record.
 */
private long[] tree_;

private Position[] positions_;

private long root_;

private bool hasRoot;

/**
 * One occurrence on an LR parser stack.
 *
 * Terminal occurrences retain only their position. Rule occurrences also
 * identify their record in the shared syntax-tree arena.
 */
public struct SyntaxTreeNode
{
    long address = -1;

    Position position;

    public bool isRule() const
    {
        return address >= 0;
    }
}

public struct SyntaxTreeCheckpoint
{
    private size_t treeLength;

    private long root;

    private bool hasRoot;
}

public void reset()
{
    tree_.length = 0;
    positions_.length = 0;
    hasRoot = false;
}

public long createRule(const size_t alternative, const(long)[] children,
    const Position position)
in (alternative > 0)
{
    const address = cast(long) tree_.length;
    const recordLength = 1 + children.length;

    tree_.length += recordLength;
    positions_.length += recordLength;
    tree_[address] = cast(long) alternative;
    positions_[address] = position;

    foreach (offset, child; children)
    {
        assert(0 <= child && child < address);
        tree_[address + 1 + offset] = child;
        positions_[address + 1 + offset] = positions_[child];
    }
    return address;
}

public SyntaxTreeNode terminal(const Position position)
{
    return SyntaxTreeNode(-1, position);
}

public SyntaxTreeNode createRuleApplication(const size_t alternative,
    const(SyntaxTreeNode)[] children, const Position position)
in (alternative > 0)
{
    size_t childCount;

    foreach (child; children)
        if (child.isRule)
            ++childCount;

    const address = cast(long) tree_.length;
    const recordLength = 1 + childCount;

    tree_.length += recordLength;
    positions_.length += recordLength;
    tree_[address] = cast(long) alternative;
    positions_[address] = position;

    size_t offset = 1;
    foreach (child; children)
    {
        if (!child.isRule)
            continue;

        assert(child.address < address);
        tree_[address + offset] = child.address;
        positions_[address + offset] = positions_[child.address];
        ++offset;
    }
    return SyntaxTreeNode(address, position);
}

public void setRoot(const long root)
in (0 <= root && root < tree_.length)
{
    root_ = root;
    hasRoot = true;
}

public SyntaxTreeCheckpoint checkpoint()
{
    return SyntaxTreeCheckpoint(tree_.length, root_, hasRoot);
}

public void rollback(const SyntaxTreeCheckpoint checkpoint)
in (checkpoint.treeLength <= tree_.length)
{
    tree_.length = checkpoint.treeLength;
    positions_.length = checkpoint.treeLength;
    root_ = checkpoint.root;
    hasRoot = checkpoint.hasRoot;
}

public long[] tree()
{
    return tree_;
}

public Position[] positions()
{
    return positions_;
}

public long root()
in (hasRoot)
{
    return root_;
}

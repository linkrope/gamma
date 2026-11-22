module gamma.runtime.SyntaxTree_test;

import gamma.runtime.SyntaxTree : checkpoint, createRule, createRuleApplication, positions,
    reset, rollback, root, setRoot, terminal, tree;
import io : Position;

@("create evaluator-compatible syntax-tree rule applications")
unittest
{
    const firstPosition = Position("input", 1, 1, "one two");
    const secondPosition = Position("input", 1, 5, "one two");

    reset;
    const firstChild = createRule(2, null, firstPosition);
    const secondChild = createRule(1, null, secondPosition);
    const parent = createRule(3, [firstChild, secondChild], firstPosition);
    setRoot(parent);

    assert(tree == [2L, 1L, 3L, firstChild, secondChild]);
    assert(positions == [firstPosition, secondPosition, firstPosition, firstPosition, secondPosition]);
    assert(root == parent);
}

@("roll back syntax-tree construction to a checkpoint")
unittest
{
    const originalPosition = Position("input", 1, 1, "one two");
    const speculativePosition = Position("input", 1, 5, "one two");

    reset;
    const original = createRule(1, null, originalPosition);
    setRoot(original);
    const beforeRepair = checkpoint;

    const speculative = createRule(2, null, speculativePosition);
    setRoot(speculative);
    rollback(beforeRepair);

    assert(tree == [1L]);
    assert(positions == [originalPosition]);
    assert(root == original);
}

@("omit terminal occurrences from direct rule applications")
unittest
{
    const position = Position("input", 1, 1, "one");

    reset;
    const child = createRuleApplication(1, null, position);
    const parent = createRuleApplication(2, [terminal(position), child, terminal(position)], position);
    setRoot(parent.address);

    assert(tree == [1L, 2L, child.address]);
    assert(positions == [position, position, position]);
    assert(root == parent.address);
}

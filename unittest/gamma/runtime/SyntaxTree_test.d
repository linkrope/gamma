module gamma.runtime.SyntaxTree_test;

import gamma.runtime.SyntaxTree : checkpoint, nodeCount, positions,
    reset, rollback, root, ruleNode, setRoot, terminalNode, tree;
import io : Position;

@("create evaluator-compatible syntax-tree rule nodes")
unittest
{
    reset;

    const firstPosition = Position("input", 1, 1, "one two");
    const firstChild = ruleNode(2, null, firstPosition);
    const secondPosition = Position("input", 1, 5, "one two");
    const secondChild = ruleNode(1, null, secondPosition);
    const parent = ruleNode(3, [firstChild, secondChild], firstPosition);

    setRoot(parent.address);

    assert(tree == [2L, 1L, 3L, firstChild.address, secondChild.address]);
    assert(positions == [firstPosition, secondPosition, firstPosition, firstPosition, secondPosition]);
    assert(nodeCount == 3);
    assert(root == parent.address);
}

@("roll back syntax-tree construction to a checkpoint")
unittest
{
    reset;

    const originalPosition = Position("input", 1, 1, "one two");
    const speculativePosition = Position("input", 1, 5, "one two");
    const original = ruleNode(1, null, originalPosition);

    setRoot(original.address);

    const beforeRepair = checkpoint;
    const speculative = ruleNode(2, null, speculativePosition);

    setRoot(speculative.address);
    rollback(beforeRepair);

    assert(tree == [1L]);
    assert(positions == [originalPosition]);
    assert(nodeCount == 1);
    assert(root == original.address);
}

@("omit terminal occurrences from direct rule nodes")
unittest
{
    reset;

    const position = Position("input", 1, 1, "one");
    const child = ruleNode(1, null, position);
    const parent = ruleNode(2, [terminalNode(position), child, terminalNode(position)], position);

    setRoot(parent.address);

    assert(tree == [1L, 2L, child.address]);
    assert(positions == [position, position, position]);
    assert(nodeCount == 2);
    assert(root == parent.address);
}

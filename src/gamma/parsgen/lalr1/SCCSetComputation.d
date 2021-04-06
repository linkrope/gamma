module gamma.parsgen.lalr1.SCCSetComputation;

import gamma.util.Indexed;

/**
 * Computation of the set-valued function F on the nodes V of a digraph
 * G=(V,E), such that, for all x,y in V, F(x) is the smallest set
 * satisfying (1) F(x) >= F'(x), and (2) F(x) >= F(y) if (x,y) in E.
 * The computation effectively computes the strongly connected components
 * of G using Tarjan's algorithm (as streamlined by Eve and Kurko-Suonio).
 * <p>
 * The digraph nodes are passed to the algorithm as an
 * <code>Indexed [] nodes</code> (which will imply the node traversal order).
 * For <code>x, y</code> from <code>nodes[]</code> it is required that
 * <code>x <> y</code> implies <code>x.index <> y.index</code>.
 *
 * @author SöKa
 */
public class SCCSetComputation
{
    /**
     * "Walks" edges in the digraph.
     */
    public interface TransitionWalker
    {
        /**
         * "Walks down" an edge <code>(x,y)</code> in the digraph.
         */
        void walk(Indexed x, Indexed y);
    }

    /**
     * Finds out the outgoing edges of a given node in the digraph.
     */
    public interface TransitionEnumerator
    {
        /**
         * Given the digraph node <code>x</code>, call
         * <code>transitionWalker(x,y)</code> for each edge <code>(x,y)</code>
         * in the digraph.
         */
        void visitNeighborsOf(Indexed x, TransitionWalker transitionWalker);
    }

    public interface SetOperator
    {
        /** Initialize F(x), i.e. compute F(x) := F'(x). */
        void initSet(Indexed x);

        /** Include F(y) in F(x), i.e. perform the assignment F(x) := F(x) + F(y). */
        void includeSet(Indexed x, Indexed y);
    }

    /**
     * Runs the algorithm to compute all sets F(x) as described in the class
     * documentation. Caller provides a <code>transitionEnumerator</code> to
     * realize the digraph's edge relation E, and a
     * <code>setOperator</code> to realize the necessary set computations.
     *
     * @param nodes The nodes of the digraph
     * @param transitionEnumerator provides digraph edges
     * @param setOperator realizes set computations
     */
    static public void computeSets(Indexed [] nodes,
        TransitionEnumerator transitionEnumerator,
        SetOperator setOperator)
    {
        auto instance = new SCCSetComputation(nodes, transitionEnumerator, setOperator);

        instance.run;
    }

    private Indexed[] nodes;

    private Indexed[] stack;

    private int top;

    private int[] low;

    private TransitionEnumerator transitionEnumerator;

    private SetOperator setOperator;

    private enum UNVISITED = -1;

    private enum DONE = int.max;

    private TransitionWalker minimizeLowxOp;

    private this(Indexed[] nodes,
        TransitionEnumerator transitionEnumerator,
        SetOperator setOperator)
    {
        this.nodes = nodes;
        this.transitionEnumerator = transitionEnumerator;
        this.setOperator = setOperator;
        this.minimizeLowxOp = new class TransitionWalker
        {
            public void walk(Indexed x, Indexed y)
            {
                traverse(y);
                setOperator.includeSet(x, y);
                if (low[x.index] < low[y.index])
                    low[x.index] = low[y.index];
            }
        };
    }

    private void traverse(Indexed x)
    {
        if (low[x.index] == UNVISITED)
        {
            stack[++top] = x;

            const depth = top;

            low[x.index] = top;
            setOperator.initSet(x);
            transitionEnumerator.visitNeighborsOf(x, minimizeLowxOp);
            if (low[x.index] == depth)
            {
                while (top > depth)
                {
                    // Set F(x) to F(y), i.e. perform the assignment F(x) := F(y).
                    // Can be realized by including F(x) into F(y).
                    setOperator.includeSet(stack[top], x);
                    low[stack[top].index] = DONE;
                    --top;
                }
                low[stack[top].index] = DONE;
                --top;
            }
        }
    }

    private void run()
    {
        import std.conv : to;

        int maxIndex = -1;

        for (int i = 0; i < nodes.length; ++i)
            if (nodes[i].index.to!int > maxIndex)
                maxIndex = nodes[i].index.to!int;

        this.stack = new Indexed[nodes.length];
        this.low = new int[maxIndex + 1];
        this.top = -1;

        for (int i = 0; i < nodes.length; ++i)
            low[nodes[i].index] = UNVISITED;
        for (int i = 0; i < nodes.length; ++i)
            traverse(nodes[i]);
    }
}

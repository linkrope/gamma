module gamma.runtime.Node;

/*
 * Created on 01.04.2005
 *
 * @author kuniss
 * Copyright 2005
 */

/**
 * Represents a runtime node the runtime syntax tree is build from.
 * All generated tools working with the syntax tree representation are based on this interface.
 * @author kuniss 01.04.2005
 */
public interface Node
{
    /**
     * Returns the ID of the grammar.Alternative represented by this node
     * @return a number representing an alternative
     */
    int alternativeID(); // meta alternatives must be indexed!

    /**
     * Returns the number of the subnode linked to this super node
     * @return the number of subnodes
     */
    int arity();

    /**
     * Returns the i-th sub node of this node.
     * @param i the count number of the node (starting with 1)
     * @return the selected tree Node
     */
    Node subNode(int i);
}

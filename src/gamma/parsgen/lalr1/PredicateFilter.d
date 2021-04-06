module gamma.parsgen.lalr1.PredicateFilter;

import gamma.grammar.Node;

/**
 * Describes the ability to decide whether a Node in a Grammar Rule right-hand side is a predicate or not.
 *
 * @author SöKa
 */
public interface PredicateFilter
{
    bool isPredicate(Node node);
}

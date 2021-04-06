module gamma.parsgen.lalr1.LR1ParserGenerator;

import gamma.grammar.Grammar;
import gamma.parsgen.lalr1.LR1ConflictResolver;
import gamma.parsgen.lalr1.OrderedLR1Tables;

public interface LR1ParserGenerator
{
    /**
     * Computes ordered *LR(1) tables. Potential conflicts are resolved
     * by the given <code>lr1ConflictResolver</code>. The resulting tables
     * represent a deterministic parser.
     * Problems are marked via <code>symbolNode.position().markError(...)</code>
     * (where <code>symbolNode</code> is an appropriate symbol occurence of the
     * <code>grammar</code>.
     * If no parser could be computed, <code>null</code> is returned.
     */
    OrderedLR1Tables computeParser(Grammar grammar, LR1ConflictResolver lr1ConflictResolver);
}

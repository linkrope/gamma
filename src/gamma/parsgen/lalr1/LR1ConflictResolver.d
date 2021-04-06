module gamma.parsgen.lalr1.LR1ConflictResolver;

import gamma.grammar.Alternative;
import gamma.grammar.Terminal;

/**
 * Controls how shift/reduce and reduce/reduce nondeterminisms in a *LR(1)
 * parser are resolved.
 */
public interface LR1ConflictResolver
{
    /**
     * Calls for resolution of a shift/reduce parser conflict:
     * The parser sees a conflict at state <code>state</code> whether to
     * shift a <code>terminal</code> or reduce an <code>alternative</code>
     * (the underlying grammar being understood).
     * @param terminal
     * @param alternative
     * @param state
     * @return <code>terminal</code> if the shift is favored; <code>alternative</code>
     *     if the reduce is favored; <code>null</code> if neither is accepted.
     */
    Object resolveShiftReduceConflict(
        Terminal terminal,
        Alternative alternative,
        size_t state);

    /**
     * Calls for resolution of a reduce/reduce parser conflict:
     * The parser sees a conflict at state <code>state</code> whether to
     * reduce an <code>alternative1</code> or reduce an <code>alternative2</code>
     * (the underlying grammar being understood).
     * @param alternative1
     * @param alternative2
     * @param terminal Look-ahead
     * @param state
     * @return <code>alternative1</code> if reducing it is favored;
     *     <code>alternative2</code> if reducing it is favored;
     *     or <code>null</code> if neither is accepted.
     */
    Object resolveReduceReduceConflict(
        Alternative alternative1,
        Alternative alternative2,
        Terminal terminal,
        size_t state);

    /**
     * Notifies that there is a parser conflict at state <code>state</code>
     * whether to halt or to reduce an <code>alternative</code>
     * (the underlying grammar being understood).
     * This indicates an ambiguity of the grammar.
     * @param alternative
     * @param state
     */
    void noteHaltConflictOn(Alternative alternative, size_t state);
}

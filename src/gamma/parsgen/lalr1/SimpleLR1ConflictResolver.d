module gamma.parsgen.lalr1.SimpleLR1ConflictResolver;

import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.Nonterminal;
import gamma.grammar.Terminal;
import gamma.parsgen.lalr1.LR1ConflictResolver;

/**
 * A standard LR(1) conflict resolver.
 *
 * @author SöKa
 */
public class SimpleLR1ConflictResolver : LR1ConflictResolver
{
    int srConflicts = 0;

    int rrConflicts = 0;

    int haltConflicts = 0;

    private Grammar grammar;

    this(Grammar grammar)
    {
        this.grammar = grammar;
    }

    public Object resolveShiftReduceConflict(Terminal terminal, Alternative alternative, size_t state)
    {
        import std.format : format;

        ++srConflicts;
        alternative.position
            .markError(format!"shift/reduce conflict at state %s for look-ahead %s"(state, terminal));
        return terminal;
    }

    public Object resolveReduceReduceConflict(Alternative alternative1, Alternative alternative2,
        Terminal terminal, size_t state)
    {
        import std.format : format;

        ++rrConflicts;
        alternative1.position
            .markError(format!"reduce/reduce conflict with '%s' for look-ahead %s"(alternative2,
                (terminal !is null) ? terminal.toString : "(null)"));

        const n1 = (cast(Nonterminal) alternative1.lhs.symbol).index;
        const n2 = (cast(Nonterminal) alternative2.lhs.symbol).index;

        if (n1 < n2)
            return alternative1;
        else if (n1 > n2)
            return alternative2;
        else
            foreach (alternative; this.grammar.ruleOf(this.grammar.nonterminal(n1)).alternatives)
            {
                if (alternative == alternative1)
                    return alternative1;
                else if (alternative == alternative2)
                    return alternative2;
            }
        return null;
    }

    public void noteHaltConflictOn(Alternative alternative, size_t state)
    {
        ++haltConflicts;
        alternative.position
            .markError("reduce/halt conflict");
    }


    public int getHaltConflicts() const
    {
        return this.haltConflicts;
    }


    public int getRrConflicts() const
    {
        return this.rrConflicts;
    }


    public int getSrConflicts() const
    {
        return this.srConflicts;
    }
}

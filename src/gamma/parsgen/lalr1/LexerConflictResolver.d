module gamma.parsgen.lalr1.LexerConflictResolver;

import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.Nonterminal;
import gamma.grammar.Terminal;
import gamma.parsgen.lalr1.LR1ConflictResolver;
import gamma.util.Position;

/**
 * Resolves lexical continuation in favor of longest match.
 */
public class LexerConflictResolver : LR1ConflictResolver
{
    private Grammar grammar;

    private Terminal tokenEnd;

    private Nonterminal[Terminal] helpersByTerminal;

    private size_t[][Nonterminal] lexicalNonterminalOwners;

    private string[] nonterminalNames;

    public this(Grammar grammar, Terminal tokenEnd, Nonterminal[Terminal] helpersByTerminal,
        size_t[][Nonterminal] lexicalNonterminalOwners, string[] nonterminalNames)
    {
        this.grammar = grammar;
        this.tokenEnd = tokenEnd;
        this.helpersByTerminal = helpersByTerminal.dup;
        this.lexicalNonterminalOwners = lexicalNonterminalOwners.dup;
        this.nonterminalNames = nonterminalNames.dup;
    }

    public Object resolveShiftReduceConflict(Terminal terminal, Alternative alternative, size_t state)
    {
        return terminal;
    }

    public Object resolveReduceReduceConflict(Alternative first, Alternative second, Terminal terminal, size_t state)
    {
        if (terminal == tokenEnd && hasDistinctCandidateOwners(first, second))
        {
            import std.format : format;

            const owners = ownersFor(first, second);

            first.position.markError(format!"ambiguous lexical nonterminals %s and %s"(
                nonterminalNames[owners[0]], nonterminalNames[owners[1]]));

            throw new Exception("ambiguous lexical nonterminals");
        }
        if (terminal != tokenEnd)
        {
            if (isTerminalHelper(first))
                return second;
            if (isTerminalHelper(second))
                return first;
        }

        foreach (alternative; grammar.ruleOf(first.lhs.nonterminal).alternatives)
        {
            if (alternative == first)
                return first;
            if (alternative == second)
                return second;
        }
        assert(false);
    }

    public void noteHaltConflictOn(Alternative alternative, size_t state)
    {
        assert(false, "unexpected lexical halt conflict");
    }

    private bool isTerminalHelper(Alternative alternative) const
    {
        foreach (helper; helpersByTerminal)
            if (helper == alternative.lhs.nonterminal)
                return true;
        return false;
    }

    private bool hasDistinctCandidateOwners(Alternative first, Alternative second) const
    {
        return ownersFor(first, second).length > 1;
    }

    private size_t[] ownersFor(Alternative first, Alternative second) const
    {
        import std.algorithm : canFind;

        size_t[] result = null;

        void appendOwners(Alternative alternative)
        {
            if (auto owners = alternative.lhs.nonterminal in lexicalNonterminalOwners)
            {
                foreach (owner; *owners)
                    if (!result.canFind(owner))
                        result ~= owner;
            }
        }

        appendOwners(first);
        appendOwners(second);
        return result;
    }
}

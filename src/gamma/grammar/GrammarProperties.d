module gamma.grammar.GrammarProperties;

import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.Node;
import gamma.grammar.Nonterminal;
import gamma.grammar.Rule;
import gamma.grammar.Symbol;
import gamma.grammar.SymbolNode;
import gamma.grammar.Terminal;
import log;
import std.algorithm;
import std.bitmanip : BitArray;
import std.range;

version (unittest) import gamma.grammar.GrammarBuilder;

// requires a (converted) grammar without EBNF expressions
public class GrammarProperties
{
    /**
     * The grammar for which all properties are computed.
     */
    private Grammar grammar_;

    private bool[Nonterminal] tokens;

    /**
     * A flag for each nonterminal which is true if the nonterminal produces the
     * empty word.
     */
    private BitArray nullableNonterminals;

    /**
     * A flag for each nonterminal which is true if the nonterminal produces
     * terminals or the empty word.
     */
    private BitArray productiveNonterminals;

    /**
     * Contains a list of alternatives for every nonterminal where it occurs on the rhs
     * <code>nontOccurrences</code> : Nonterminal.index() -> List of Alternatives
     */
    private Alternative[][] nontOccurrences;

    /**
     * Maps each (lhs) Nonterminal.index() to the first (or "simplest")
     * Alternative which proved its left hand side to be productive.
     */
    private Alternative[] firstProductiveAlternative;

    /**
     * A flag for each nonterminal which is true if the nonterminal is reachable
     * from the grammar's start symbol by applying derivation rules.
     */
    private BitArray reachableNonterminals;

    /**
     * A flag for each terminal which is true if the terminal is reachable from
     * the grammar's start symbol by applying derivation rules.
     */
    private BitArray reachableTerminals;

    /**
     * A flag for each nonterminal which is true if the nonterminal defines
     * a predicate
     */
    private BitArray predicateNonterminals;

    private BitArray lexicalNonterminals;

    public this(Grammar grammar, bool[Nonterminal] tokens = null)
    {
        this.grammar_ = grammar;
        this.tokens = tokens;
    }

    /**
     * Returns whether the symbol is nullable or not.
     */
    public bool isNullable(Symbol symbol)
    in (cast(Nonterminal) symbol || cast(Terminal) symbol)
    {
        if (nullableNonterminals.empty)
            computeNullablesAndProductives;

        return cast(Nonterminal) symbol
            && nullableNonterminals[(cast(Nonterminal) symbol).index];
    }

    /**
     * Returns whether the symbol is productive or not.
     */
    public bool isProductive(Symbol symbol)
    in (cast(Nonterminal) symbol || cast(Terminal) symbol)
    {
        if (productiveNonterminals.empty)
            computeNullablesAndProductives;

        return cast(Terminal) symbol
            || productiveNonterminals[(cast(Nonterminal) symbol).index];
    }

    /**
     * Returns whether the symbol can be reached from the grammar's
     * start symbol by applying derivation rules.
     */
    public bool isReachable(Symbol symbol)
    in (cast(Nonterminal) symbol || cast(Terminal) symbol)
    {
        if (reachableNonterminals.empty)
            computeReachables;

        if (cast(Nonterminal) symbol)
            return reachableNonterminals[(cast(Nonterminal) symbol).index];
        else
            return reachableTerminals[(cast(Terminal) symbol).index];
    }

    /**
     * Returns true if the given symbol is strong nullable.
     * A symbol is strong nullable if and only if it derives only the empty word.
     *
     * @author kuniss 16.10.2004
     */
    public bool isStrongNullable(Symbol symbol)
    {
        if (this.predicateNonterminals.empty)
            computeStrongNullables;

        return (cast(Nonterminal) symbol)
            && this.predicateNonterminals[(cast(Nonterminal) symbol).index];
    }

    public bool isLexicalNonterminal(Symbol symbol)
    {
        if (this.lexicalNonterminals.empty)
            computeLexicalNonterminals;

        return (cast(Nonterminal) symbol)
            && this.lexicalNonterminals[(cast(Nonterminal) symbol).index];
    }

    /**
     * Return whether the given Alternative is the first (or "simplest") in its
     * Rule structure which has been proven to be productive.
     */
    public bool isFirstProductiveAlternative(Alternative alternative)
    {
        if (productiveNonterminals.empty)
            computeNullablesAndProductives;

        return firstProductiveAlternative[(cast(Nonterminal) alternative.lhs.symbol).index] == alternative;
    }

    /**
     * Return the first (or "simplest") Alternative in the given Rule structure
     * which has been proven to be productive.
     */
    public Alternative firstProductiveAlternativeFor(Rule rule)
    {
        if (productiveNonterminals.empty)
            computeNullablesAndProductives;

        Alternative[] alternatives = rule.alternatives;

        if (alternatives.empty)
            return null;

        return firstProductiveAlternative[(cast(Nonterminal) alternatives.front.lhs.symbol).index];
    }

    /**
     * Returns whether the grammar is reduced.
     */
    public bool isReduced()
    {
        if (reachableNonterminals.empty)
            computeReachables;

        if (productiveNonterminals.empty)
            computeNullablesAndProductives;

        return grammar.terminals.all!(terminal => isReachable(terminal))
            && grammar.nonterminals.all!(nonterminal => isReachable(nonterminal))
            && grammar.nonterminals.all!(nonterminal => isProductive(nonterminal));
    }

    /**
     * Creates the map this.nontOccurrences,
     * a list of alternatives for every nonterminal where it occurs on the rhs
     * @see GrammarProperties.nontOccurrences
     */
    private void createNontOccurrences()
    {
        this.nontOccurrences = new Alternative[][this.grammar_.nonterminals.length];
        foreach (lhs; this.grammar_.nonterminals)
        {
            foreach (alternative; this.grammar_.ruleOf(lhs).alternatives)
            {
                foreach (i; 0 .. alternative.rhs.length)
                {
                    auto node = cast(Node) alternative.rhs[i];

                    if (cast(SymbolNode) node)
                    {
                        auto symbol = cast(Symbol) (cast(SymbolNode) node).symbol;

                        if (cast(Nonterminal) symbol)
                            this.nontOccurrences[(cast(Nonterminal) symbol).index] ~= alternative;
                    }
                }
            }
        }
    }

    /**
     * Computes the set of nullable and productive nonterminals.
     */
    private void computeNullablesAndProductives()
    {
        /*
         * create map:
         * <code>alt2Count</code> : Alternative -> number of symbols in the alternative
         */
        size_t[Alternative] alt2Count;

        foreach (lhs; this.grammar_.nonterminals)
        {
            foreach (alternative; this.grammar_.ruleOf(lhs).alternatives)
                alt2Count[alternative] = alternative.rhs.length;
        }
        if (this.nontOccurrences.empty)
            createNontOccurrences;

        firstProductiveAlternative = new Alternative[this.grammar_.nonterminals.length];

        /*
         * Determine nullable nonterminals.
         * - the stack <code>nontStack</code> contains all nonterminals
         *   which have been marked as nullable and for which this property
         *   has to be propagated to the alternatives where they occur on
         *   right hand sides;
         * - alt2Count contains the number of symbols which
         *   are potentially not nullable
         * 1. all nonterminals with empty alternatives on the right
         *     hand side are marked and put on a stack
         * 2. the nullable property is propagated until the stack is empty
         */
        nullableNonterminals = BitArray();
        nullableNonterminals.length = this.grammar_.nonterminals.length;

        Nonterminal[] nontStack;

        // find all empty alternatives,
        // initialize nullableNonterminals with them and put them on the stack
        foreach (nont; this.grammar_.nonterminals)
        {
            foreach (alternative; this.grammar_.ruleOf(nont).alternatives)
            {
                if (alt2Count[alternative] == 0 && !nullableNonterminals[nont.index])
                {
                    // empty alternative
                    nontStack ~= nont;
                    nullableNonterminals[nont.index] = true;
                    if (firstProductiveAlternative[nont.index] is null)
                        firstProductiveAlternative[nont.index] = alternative;
                }
            }
        }

        // propagate nullable nonterminal
        while (!nontStack.empty)
        {
            Nonterminal nont = nontStack.back;

            nontStack.popBack;
            foreach (alternative; nontOccurrences[nont.index])
            {
                size_t count = alt2Count[alternative];

                --count;
                alt2Count[alternative] = count;
                if (count == 0) // the alternative is nullable
                {
                    // mark the lhs nonterminal and put it on the stack
                    assert(cast(Nonterminal) alternative.lhs.symbol);

                    auto lhs = cast(Nonterminal) alternative.lhs.symbol;

                    if (!nullableNonterminals[lhs.index])
                    {
                        nontStack ~= lhs;
                        nullableNonterminals[lhs.index] = true;
                        if (firstProductiveAlternative[lhs.index] is null)
                            firstProductiveAlternative[lhs.index] = alternative;
                    }
                }
            }
        }

        trace!"nullable nonterminals:%-(\n%s%)"
            (this.grammar_.nonterminals.filter!(nonterminal => isNullable(nonterminal)));

        /*
         * Compute productive nonterminals.
         * - the stack <code>nontStack</code> is reused but now it contains
         *   all nonterminals which has been marked as productive and for
         *   which this property has to be propagated to the alternatives
         *   where they occur on right hand sides.
         * 1. all nullable nonterminals are productive
         * 2. all nonterminals which produces terminals directly are marked
         *     as productive and put on the stack
         * 3. the productive property is propagated until the stack is empty
         */
        productiveNonterminals = BitArray();
        productiveNonterminals.length = this.grammar_.nonterminals.length;

        // initialize productiveNonterminals with nullable nonterminals
        foreach (nont; this.grammar_.nonterminals)
        {
            if (nullableNonterminals[nont.index])
                productiveNonterminals[nont.index] = true;
        }

        // initialize productiveNonterminals with nonterminals which produces
        // terminals directly
        foreach (nont; this.grammar_.nonterminals)
        {
            foreach (alternative; this.grammar_.ruleOf(nont).alternatives)
            {
                size_t t = 0; // the number of terminals in the alternative

                foreach (node; alternative.rhs)
                    if (cast(SymbolNode) node)
                        if (cast(Terminal) (cast(SymbolNode) node).symbol)
                            ++t;
                if (t > 0)
                {
                    t = alt2Count[alternative] - t;
                    alt2Count[alternative] = t;
                    if (t == 0 && !productiveNonterminals[nont.index])
                    {
                        nontStack ~= nont;
                        productiveNonterminals[nont.index] = true;
                        if (firstProductiveAlternative[nont.index] is null)
                            firstProductiveAlternative[nont.index] = alternative;
                    }
                }
            }
        }

        // propagate productive nonterminals (make transitive closure)
        while (!nontStack.empty)
        {
            Nonterminal nont = nontStack.back;

            nontStack.popBack;
            foreach (alternative; nontOccurrences[nont.index])
            {
                size_t count = alt2Count[alternative];

                --count;
                alt2Count[alternative] = count;
                if (count == 0)
                // the alternative is productive, mark the lhs nonterminal and
                // put it on the stack
                {
                    assert(cast(Nonterminal) alternative.lhs.symbol);

                    auto lhs = cast(Nonterminal) alternative.lhs.symbol;

                    if (!productiveNonterminals[lhs.index])
                    {
                        nontStack ~= lhs;
                        productiveNonterminals[lhs.index] = true;
                        if (firstProductiveAlternative[lhs.index] is null)
                            firstProductiveAlternative[lhs.index] = alternative;
                    }
                }
            }
        }

        trace!"productive nonterminals:%-(\n%s%)"
            (this.grammar_.nonterminals.filter!(nonterminal => isProductive(nonterminal)));
    }

    /**
     * Computes the set <code>reachableNonterminals</code> of nonterminals
     * reached from the grammar's start symbol by applying derivation rules.
     */
    private void computeReachables()
    {
        reachableNonterminals = BitArray();
        reachableNonterminals.length = this.grammar_.nonterminals.length;
        reachableTerminals = BitArray();
        reachableTerminals.length = this.grammar_.terminals.length;

        traverseReachables(this.grammar_.startSymbol);

        trace!"reachable nonterminals:%-(\n%s%)"
            (this.grammar_.nonterminals.filter!(nonterminal => isReachable(nonterminal)));
        trace!"reachable terminals:%-(\n%s%)"
            (this.grammar_.terminals.filter!(terminal => isReachable(terminal)));
    }

    /**
     * Depth-first traversal of the symbols occurring on right-hand sides
     * (if any) of the given <code>symbol</code>.
     */
    private void traverseReachables(Symbol symbol)
    in (cast(Nonterminal) symbol || cast(Terminal) symbol)
    {
        if (cast(Nonterminal) symbol)
        {
            auto nonterminal = cast(Nonterminal) symbol;

            if (!reachableNonterminals[nonterminal.index])
            {
                reachableNonterminals[nonterminal.index] = true;

                foreach (alternative; this.grammar_.ruleOf(nonterminal).alternatives)
                    foreach (node; alternative.rhs)
                    {
                        assert(cast(SymbolNode) node);

                        traverseReachables(cast(Symbol) (cast(SymbolNode) node).symbol);
                    }
            }
        }
        else
        {
            if (!reachableTerminals[(cast(Terminal) symbol).index])
                reachableTerminals[(cast(Terminal) symbol).index] = true;
        }
    }

    /**
     * Computes the lexical nonterminals by depth-first traversal
     * starting from the nonterminals marked as tokens.
     */
    private void computeLexicalNonterminals()
    {
        this.lexicalNonterminals = BitArray();
        this.lexicalNonterminals.length = this.grammar_.nonterminals.length;

        foreach (nonterminal, value; this.tokens)
            if (value)
                traverseLexicalNonterminals(nonterminal);

        trace!"lexical nonterminals:%-(\n%s%)"
            (this.grammar_.nonterminals.filter!(nonterminal => isLexicalNonterminal(nonterminal)));
    }

    private void traverseLexicalNonterminals(Nonterminal nonterminal)
    {
        if (!this.lexicalNonterminals[nonterminal.index])
        {
            this.lexicalNonterminals[nonterminal.index] = true;
            foreach (alternative; this.grammar_.ruleOf(nonterminal).alternatives)
                foreach (node; alternative.rhs)
                    if (cast(SymbolNode) node && cast(Nonterminal) (cast(SymbolNode) node).symbol)
                        traverseLexicalNonterminals(cast(Nonterminal) (cast(SymbolNode) node).symbol);
        }
    }

    /**
     * Computes the set of strong nullable nonterminals
     * TODO has to be integrated into computeNullablesAndProductives()
     * @author kuniss 16.10.2004
     */
    private void computeStrongNullables()
    {
        if (this.nontOccurrences.empty)
            createNontOccurrences;

        Nonterminal[] nonStrongNullableStack; // all nonterminals which are definitely not strong nullable
        BitArray strongNullablesComplementSet;

        strongNullablesComplementSet.length = this.grammar_.nonterminals.length;

        // initialize stack and the complement set
        foreach (lhs; this.grammar_.nonterminals)
        {
            if (!isNullable(lhs))
            {
                nonStrongNullableStack ~= lhs;
                strongNullablesComplementSet[lhs.index] = true;
            }
            else
            {
                 foreach (alternative; this.grammar_.ruleOf(lhs).alternatives)
                 {
                    foreach (node; alternative.rhs)
                    {
                        if (cast(SymbolNode) node)
                        {
                            auto symbol = cast(Symbol) (cast(SymbolNode) node).symbol;

                            if (cast(Terminal) symbol)
                            {
                                if (!strongNullablesComplementSet[lhs.index])
                                {
                                    nonStrongNullableStack ~= lhs;
                                    strongNullablesComplementSet[lhs.index] = true;
                                }
                                break; // node loop
                            }
                        }
                    }
                }
            }
        }

        while (!nonStrongNullableStack.empty)
        {
            // assert nonStrongNullableStack.top instanceof Nonterminal
            Nonterminal nont = nonStrongNullableStack.back;
            Alternative[] altList = this.nontOccurrences[nont.index];

            nonStrongNullableStack.popBack;
            foreach (alt; altList)
            {
                // assert alt.lhs.symbol instanceof Nonterminal
                auto lhs = cast(Nonterminal) alt.lhs.symbol;

                if (!strongNullablesComplementSet[lhs.index])
                {
                    nonStrongNullableStack ~= lhs;
                    strongNullablesComplementSet[lhs.index] = true;
                }
            }

            this.predicateNonterminals = this.productiveNonterminals.dup;
            this.predicateNonterminals -= strongNullablesComplementSet;
        }

        trace!"predicates:%-(\n%s%)"
            (this.grammar_.nonterminals.filter!(nonterminal => isStrongNullable(nonterminal)));
    }

    public Grammar grammar()
    {
        return this.grammar_;
    }
}

@("compute properties of degenerate grammar")
unittest
{
    with (TestGrammarBuilder())
    {
        rule("A: A");
        rule("B: | B");

        with (new GrammarProperties(grammar))
        {
            assert(!isNullable(symbol("A")));
            assert(isNullable(symbol("B")));
            assert(isStrongNullable(symbol("B")));

            assert(!isProductive(symbol("A")));
            assert(isProductive(symbol("B")));

            assert(isReachable(symbol("A")));
            assert(!isReachable(symbol("B")));

            assert(!isReduced);
        }
    }
}

@("compute properties of grammar from Tremblay and Sorenson")
unittest
{
    with (TestGrammarBuilder())
    {
        rule("G: E = E | f");
        rule("E: T | E + T");
        rule("T: f | T * f");

        with (new GrammarProperties(grammar))
        {
            assert(!isNullable(symbol("G")));
            assert(!isNullable(symbol("E")));
            assert(!isNullable(symbol("T")));
            assert(!isNullable(symbol("f")));
            assert(!isNullable(symbol("=")));
            assert(!isNullable(symbol("+")));
            assert(!isNullable(symbol("*")));

            assert(isProductive(symbol("G")));
            assert(isProductive(symbol("E")));
            assert(isProductive(symbol("T")));
            assert(isProductive(symbol("f")));
            assert(isProductive(symbol("=")));
            assert(isProductive(symbol("+")));
            assert(isProductive(symbol("*")));

            assert(isReachable(symbol("G")));
            assert(isReachable(symbol("E")));
            assert(isReachable(symbol("T")));
            assert(isReachable(symbol("f")));
            assert(isReachable(symbol("=")));
            assert(isReachable(symbol("+")));
            assert(isReachable(symbol("*")));

            assert(isReduced);
        }
    }
}

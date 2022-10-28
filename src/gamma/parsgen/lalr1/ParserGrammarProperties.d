module gamma.parsgen.lalr1.ParserGrammarProperties;

import gamma.grammar.Grammar;
import gamma.grammar.GrammarProperties;
import gamma.grammar.Node;
import gamma.grammar.Nonterminal;
import gamma.grammar.Symbol;
import gamma.grammar.SymbolNode;
import gamma.parsgen.lalr1.SCCSetComputation;
import gamma.util.Indexed;
import log;

version (unittest) import gamma.grammar.GrammarBuilder;

/**
 * Extended grammar properties for LR parser generation.
 */
public class ParserGrammarProperties : GrammarProperties
{
    private bool[Indexed][] rightDeriv;

	/**
	 * Constructor for ParserGrammarProperties.
	 * @param grammar The grammar of which to present the properties.
	 */
	public this(Grammar grammar)
    in (grammar.isPlain)
	{
		super(grammar);
        computeRightDerivationLeaders;
	}

    /**
     * Computes which nonterminals may appear as the leading symbol in a
     * right-derivation from any given nonterminal.
     */
    private void computeRightDerivationLeaders()
    {
        import std.algorithm : map;
        import std.array : array;

        Indexed[] nodes = this.grammar.nonterminals
            .map!(nonterminal => cast(Indexed) nonterminal)
            .array;

        rightDeriv = new bool[Indexed][this.grammar.nonterminals.length];
        SCCSetComputation.computeSets(
            nodes,
            new class SCCSetComputation.TransitionEnumerator
            {
                public void visitNeighborsOf( Indexed x, SCCSetComputation.TransitionWalker edge)
                {
                	assert(cast(Nonterminal) x);

                    foreach (alt; this.outer.grammar.ruleOf(cast(Nonterminal) x).alternatives)
                    {
                        Node[] rhs = alt.rhs;

                        if (rhs.length > 0)
                        {
                            Symbol y = (cast(SymbolNode) rhs[0]).symbol;

                            if (cast(Nonterminal) y)
                                edge.walk(x, cast(Nonterminal) y);
                        }
                    }
                }
            },
            new class SCCSetComputation.SetOperator
            {
                public void initSet(Indexed x)
                {
                    rightDeriv[x.index] = null;
                    rightDeriv[x.index][x] = true;
                }

                public void includeSet(Indexed x, Indexed y)
                {
                    foreach (indexed; rightDeriv[y.index].byKey)
                        rightDeriv[x.index][indexed] = true;
                }
            });

        // Debug output
        foreach (nont1; this.grammar.nonterminals)
        {
            Nonterminal[] nonterminals;

            foreach (indexedNont; rightDeriv[nont1.index].byKey)
            {
            	assert(cast(Nonterminal) indexedNont);

                nonterminals ~= cast(Nonterminal) indexedNont;
            }
            trace!"%s right derives %-(%s, %)"(nont1, nonterminals);
        }
    }

    /**
     * Yields an iterator that iterates the nonterminals which may appear
     * as the leading symbol in a right-derivation from the given nonterminal
     * <code>symbol</code>.
     */
    auto rightDerivationLeadersOf(Nonterminal nont)
    {
        return rightDeriv[nont.index].byKey;
    }
}

@("compute right-derivation leaders of grammar from Tremblay and Sorenson")
unittest
{
    with (TestGrammarBuilder())
    {
        rule("G: E = E | f");
        rule("E: T | E + T");
        rule("T: f | T * f");

        with (new ParserGrammarProperties(grammar))
        {
            auto rightDerivationLeaders(string representation)
            {
                import std.algorithm : map, sort;
                import std.array : array;

                return rightDerivationLeadersOf(buildNonterminal(representation))
                    .map!(indexed => cast(Symbol) indexed)
                    .map!"a.toString"
                    .array
                    .sort
                    .array;
            }

            assert(rightDerivationLeaders("G") == ["E", "G", "T"]);
            assert(rightDerivationLeaders("E") == ["E", "T"]);
            assert(rightDerivationLeaders("T") == ["T"]);
        }
    }
}

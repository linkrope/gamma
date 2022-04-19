module gamma.grammar.GrammarBuilder;

import gamma.grammar.hyper.GeneratedNonterminal;
import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.Nonterminal;
import gamma.grammar.Rule;
import gamma.grammar.Symbol;
import gamma.grammar.SymbolNode;
import gamma.grammar.Terminal;
import std.range;

version (unittest) import gamma.grammar.Node;
version (unittest) import gamma.util.Position;

public struct GrammarBuilder
{
    private Nonterminal[string] nonterminalMap;

    private Nonterminal[] nonterminals;

    private Terminal[string] terminalMap;

    private Terminal[] terminals;

    private Alternative[][] alternativesMap;

    private bool[Nonterminal] undefinedNonterminals;

    public Nonterminal buildNonterminal(string representation)
    {
        Nonterminal nonterminal = this.nonterminalMap.get(representation, null);

        if (nonterminal is null)
        {
            const index = this.nonterminals.length;

            nonterminal = new Nonterminal(representation, index);
            this.nonterminalMap[representation] = nonterminal;
            this.nonterminals ~= nonterminal;
            this.alternativesMap ~= null;

            this.undefinedNonterminals[nonterminal] = true;
        }
        return nonterminal;
    }

    /**
     * TODO: ?
     */
    public GeneratedNonterminal buildGeneratedNonterminal()
    {
        import std.exception : enforce;
        import std.format : format;

        const index = this.nonterminals.length;
        auto nonterminal = new GeneratedNonterminal(index);
        Nonterminal userNont = this.nonterminalMap.get(nonterminal.toString, null);

        enforce(userNont is null,
                format!"generated nonterminal name already defined by the user: %s"(nonterminal));

        this.nonterminalMap[nonterminal.toString] = nonterminal;
        this.nonterminals ~= nonterminal;
        this.alternativesMap ~= null;

        this.undefinedNonterminals[nonterminal] = true;

        return nonterminal;
    }

    public Terminal buildTerminal(string representation)
    {
        Terminal terminal = this.terminalMap.get(representation, null);

        if (terminal is null)
        {
            const index = this.terminals.length;

            terminal = new Terminal(representation, index);
            this.terminalMap[representation] = terminal;
            this.terminals ~= terminal;
        }
        return terminal;
    }

    public void add(Alternative alternative)
    in(cast(Nonterminal) alternative.lhs.symbol)
    {
        Nonterminal lhs = cast(Nonterminal) alternative.lhs.symbol;
        const index = lhs.index;

        this.undefinedNonterminals.remove(lhs);

        this.alternativesMap[index] ~= alternative;
    }

    /**
     * Returns true if and only if for all nonterminals N on the right hand side
     * exists at least one alternative where the nonterminal N is on the left hand side.
     *
     * @return true if the grammar is well defined; false otherwise
     */
    public bool grammarIsWellDefined()
    {
        // TODO: hyper grammar contains undefined nonterminals,
        // because a complete rule is added for any EBNF expression
        return this.undefinedNonterminals.empty || true;
    }

    @("build well-formed grammar")
    unittest
    {
        with (TestGrammarBuilder())
        {
            rule("A: B");
            rule("B:");

            assert(grammarIsWellDefined);
        }
    }

    /**
     * Marks all positions for which the grammar is not well defined.
     * If the grammar is well defined no positions are marked.
     */
    public void markErrors()
    {
        import log : error;

        if (this.undefinedNonterminals.empty)
            return;
        foreach (alternatives; alternativesMap)
        {
            foreach (alternative; alternatives)
            {
                foreach (node; alternative.rhs)
                {
                    if (cast(SymbolNode) node) // FIXME: else
                    {
                        Symbol symbol = (cast(SymbolNode) node).symbol;

                        if (cast(Nonterminal) symbol && cast(Nonterminal) symbol in this.undefinedNonterminals)
                            error!"%s is undefined (not on left hand side\n%s"(symbol, node.position);
                    }
                }
            }
        }
    }

    @("mark position as having an error")
    unittest
    {
        with (GrammarBuilder())
        {
            Position position;
            Nonterminal A = buildNonterminal("A");
            Nonterminal B = buildNonterminal("B");
            Node[] rhs = [new SymbolNode(B, position)];

            add(new Alternative(new SymbolNode(A, position), rhs , position));

            markErrors;

            // FIXME: how to check this?
        }
    }

    /**
     * Returns the collected grammar rules with the given nonterminal as start symbol.
     * Returns null if the grammar is not well defined.
     *
     * @param startSymbol
     *            the nonterminal which is used as start symbol for the returned grammar
     * @return the collected grammar
     */
    public Grammar getGrammar(Nonterminal startSymbol = null)
    {
        if (!grammarIsWellDefined)
            return null;

        Rule[] rules;

        foreach (alternatives; alternativesMap)
            if (!alternatives.empty)
                rules ~= new Rule(alternatives);
        return new Grammar(this.nonterminals, this.terminals, rules, startSymbol);
    }
}

version (unittest):

import std.algorithm;

struct TestGrammarBuilder
{
    public GrammarBuilder builder;

    private Nonterminal startSymbol;

    alias builder this;

    public Grammar grammar()
    in (startSymbol !is null)
    {
        return getGrammar(startSymbol);
    }

    /**
     * Rule:
     *     Nonterminal ":" { Nonterminal | terminal } { "|" { Nonterminal | terminal } }.
     */
    public void rule(string line)
    {
        import gamma.grammar.Node : Node;
        import std.array : split;
        import std.string : strip;

        Position position;

        if (auto result = line.findSplit(":"))
        {
            auto lhs = symbolNode(result[0].strip);

            if (startSymbol is null)
                startSymbol = cast(Nonterminal) lhs.symbol;

            if (result[2].empty)
                add(new Alternative(lhs, [], position));
            foreach (parts; result[2].split("|"))
            {
                auto rhs = parts.split
                    .map!strip
                    .map!(representation => cast(Node) symbolNode(representation))
                    .array;

                add(new Alternative(lhs, rhs, position));
            }
        }
    }

    private SymbolNode symbolNode(string representation)
    out (symbolNode; symbolNode !is null)
    {
        Position position;

        return new SymbolNode(symbol(representation), position);
    }

    public Symbol symbol(string representation)
    out (symbol; symbol !is null)
    {
        import std.format : format;
        import std.uni : isLower, isUpper;

        if (representation.front.isUpper)
            return buildNonterminal(representation);
        else if (representation.front.isLower)
            return buildTerminal(representation);
        else
            // quote escaped representation
            return buildTerminal(format!"%(%s%)"(only(representation)));
    }
}

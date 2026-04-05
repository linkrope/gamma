module gamma.input.earley.Parser;

import gamma.grammar.affixes.Composite;
import gamma.grammar.affixes.Term;
import gamma.grammar.affixes.Variable;
import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.GrammarBuilder;
import gamma.grammar.Node;
import gamma.grammar.Nonterminal;
import gamma.grammar.Symbol;
import gamma.grammar.SymbolNode;
import gamma.grammar.Terminal;
import gamma.input.earley.AffixForm;
import gamma.input.earley.Item;
import gamma.input.earley.ItemSet;
import gamma.util.Position;
import std.range;

/**
 * If the item is of the form [ <i>B</i> &rarr; &beta; &bull;, <i>k</i> ] then for each item [ <i>A</i> &rarr;
 * &alpha; &bull; <i>B</i> &gamma;, <i>j</i> ] in the Earley set denoted by <i>k</i> an item [ <i>A</i> &rarr;
 * &alpha; <i>B</i> &bull; &gamma;, <i>j</i> ] is added to the current Earley set.
 *
 * If the item is of the form [ <i>A</i> &rarr; &alpha; &bull; <i>B</i> &gamma;, <i>j</i> ] then for each alternative
 * <i>B</i> &rarr; &beta; an item [ <i>B</i> &rarr; &bull; &beta;, <i>k</i> ] is added to the current Earley set,
 * which is denoted by <i>k</i>.
 *
 * If the item is of the form [ <i>A</i> &rarr; &alpha; &bull; <i>X</i> &gamma;, <i>i</i> ] where <i>X</i> equals
 * the current symbol then an item [ <i>A</i> &rarr; &alpha; <i>X</i> &bull; &gamma;, <i>i</i> ] is added to the next
 * Earley set.
 */
public class Parser
{
    private Grammar grammar;

    // variables from the affix form, consumed back-to-front
    private Variable[] variables;

    /**
     * @param grammar
     */
    public this(Grammar grammar)
    {
        this.grammar = grammar;
    }

    /**
     * @param startSymbol
     * @param affixForm
     * @return
     */
    public Term parse(Nonterminal startSymbol, AffixForm affixForm)
    {
        import log : error;

        GrammarBuilder grammarBuilder;
        Terminal endSymbol = grammarBuilder.buildTerminal("$");
        Node[] rhs;

        rhs ~= new SymbolNode(startSymbol, Position());
        rhs ~= new SymbolNode(endSymbol, Position());

        Nonterminal augmentedStartSymbol = grammarBuilder.buildNonterminal("S'");
        Alternative alternative = new Alternative(new SymbolNode(augmentedStartSymbol, Position()), rhs, Position());
        SymbolNode[] symbolNodes = affixForm.symbolNodes;

        symbolNodes ~= new SymbolNode(endSymbol, Position());

        ItemSet itemSet = ItemSet.initialItemSet(alternative, grammar);

        foreach (symbolNode; symbolNodes)
        {
            Symbol symbol = symbolNode.symbol;

            itemSet = ItemSet.nextItemSet(itemSet, symbol, grammar);

            if (itemSet.items.empty)
            {
                error!"syntax error: unexpected %s\n%s"(symbol, symbolNode.position);
                return null;
            }
        }
        if (affixForm.variables !is null)
            this.variables = affixForm.variables;
        if (itemSet.items.empty)
            return null;
        else
            return term(itemSet.items[0].prevItem);
    }

    public Term term(Item item)
    in (cast(Nonterminal) item.prevItem.symbol)
    {
        import std.array : array;

        if (item.subItem is null)
        {
            Variable variable = this.variables.back;

            assert(cast(Nonterminal) item.prevItem.symbol == variable.nonterminal);
            this.variables.popBack;
            return variable;
        }
        else
        {
            Term[] terms;

            for (item = item.subItem; item.prevItem !is null; item = item.prevItem)
                if (cast(Nonterminal) item.prevItem.symbol)
                    terms ~= term(item);
            terms = terms.retro.array;
            return new Composite(item.alternative, terms);
        }
    }
}

@("parse affix form")
unittest
{
    import gamma.grammar.GrammarBuilder : TestGrammarBuilder;
    import gamma.input.earley.AffixForm : affixForm;

    with (TestGrammarBuilder())
    {
        rule("S:");
        rule("S: a S b");

        Nonterminal startSymbol = cast(Nonterminal) symbol("S");
        const term = new Parser(grammar)
            .parse(startSymbol, grammar.affixForm("a S b"));

        assert(term !is null);
        assert(cast(Composite) term !is null);
    }
}

@("parse single variable")
unittest
{
    import gamma.grammar.GrammarBuilder : TestGrammarBuilder;
    import gamma.input.earley.AffixForm : affixForm;

    with (TestGrammarBuilder())
    {
        rule("S:");
        rule("S: a S b");

        Nonterminal startSymbol = cast(Nonterminal) symbol("S");
        const term = new Parser(grammar)
            .parse(startSymbol, grammar.affixForm("!S1"));

        assert(term !is null);
        assert(cast(Variable) term !is null);
    }
}

@("parse syntax error")
unittest
{
    import gamma.grammar.GrammarBuilder : TestGrammarBuilder;
    import gamma.input.earley.AffixForm : affixForm;

    with (TestGrammarBuilder())
    {
        rule("S:");
        rule("S: a S b");

        Nonterminal startSymbol = cast(Nonterminal) symbol("S");
        const term = new Parser(grammar)
            .parse(startSymbol, grammar.affixForm("b"));

        assert(term is null);
    }
}

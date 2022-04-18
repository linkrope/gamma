module gamma.input.earley.Parser;

import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.GrammarBuilder;
import gamma.grammar.Node;
import gamma.grammar.Nonterminal;
import gamma.grammar.Symbol;
import gamma.grammar.SymbolNode;
import gamma.grammar.Terminal;
import gamma.grammar.affixes.Composite;
import gamma.grammar.affixes.Term;
import gamma.grammar.affixes.Variable;
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

    private Variable[] variablesIterator;

    // TODO: eliminate attributes 'startSymbol' and 'endSymbol'

    private Nonterminal startSymbol;

    private Terminal endSymbol;

    /**
     * @param grammar
     */
    public this(Grammar grammar)
    {
        this.grammar = grammar;

        GrammarBuilder grammarBuilder;

        this.startSymbol = grammarBuilder.buildNonterminal("S'");
        this.endSymbol = grammarBuilder.buildTerminal("$");
    }

    /**
     * @param startSymbol
     * @param affixForm
     * @return
     */
    public Term parse(Nonterminal startSymbol, AffixForm affixForm)
    {
        Node[] rhs;

        rhs ~= new SymbolNode(startSymbol, Position());
        rhs ~= new SymbolNode(this.endSymbol, Position());

        Alternative alternative = new Alternative(new SymbolNode(this.startSymbol, Position()), rhs, Position());
        SymbolNode[] symbolNodes = affixForm.symbolNodes;

        symbolNodes ~= new SymbolNode(this.endSymbol, Position());

        ItemSet itemSet = ItemSet.initialItemSet(alternative, grammar);

        foreach (symbolNode; symbolNodes)
        {
            Symbol symbol = symbolNode.symbol;

            itemSet = ItemSet.nextItemSet(itemSet, symbol, grammar);

            // TODO: report syntax errors
        }
        if (affixForm.variables !is null)
            this.variablesIterator = affixForm.variables;
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
            Variable variable = this.variablesIterator.back;

            assert(cast(Nonterminal) item.prevItem.symbol == variable.nonterminal);

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

module gamma.input.earley.Item;

import gamma.grammar.Alternative;
import gamma.grammar.Node;
import gamma.grammar.Nonterminal;
import gamma.grammar.Symbol;
import gamma.grammar.SymbolNode;
import gamma.input.earley.ItemSet;

/**
 * This class represents an Earley item
 *   [ <i>A</i> &rarr; &alpha; &bull; &beta;, <i>j</i> ],
 * which means that &alpha; has been recognized since the construction of the Earley set
 * denoted by <i>j</i>.
 * <p>
 * Predecessor links as well as causal links between items are added to be able to reconstruct
 * a derivation. Each item of the form
 *   [ <i>A</i> &rarr; &alpha; <i>X</i> &bull; &gamma;, <i>j</i> ]
 * is linked to a predecessor
 *   [ <i>A</i> &rarr; &alpha; &bull; <i>X</i> &gamma;, <i>j</i> ].
 * Furthermore, each item of the form
 *   [ <i>A</i> &rarr; &alpha; <i>B</i> &bull; &gamma;, <i>j</i> ]
 * is linked to an item
 *   [ <i>B</i> &rarr; &beta; &bull;, <i>k</i> ]
 * by which it has been added in the completer step.
 */
class Item
{
    private Alternative alternative_;

    private int index;

    private Symbol symbol_;

    private ItemSet parent_;

    private Item prevItem_;

    private Item subItem_;

    public static Item initialItem(Alternative alternative, ItemSet parent)
    {
        return new Item(alternative, parent, null, null);
    }

    public static Item nextItem(Item prevItem, Item subItem)
    in (!prevItem.isFinal)
    in (subItem is null || cast(Nonterminal) prevItem.symbol_)
    {
        return new Item(prevItem.alternative_, prevItem.parent_, prevItem, subItem);
    }

    private this(Alternative alternative, ItemSet parent, Item prevItem, Item subItem)
    {
        this.alternative_ = alternative;
        if (prevItem is null)
            this.index = 0;
        else
            this.index = prevItem.index + 1;
        if (this.index < alternative.rhs.length)
            this.symbol_ = (cast(SymbolNode) alternative.rhs[this.index]).symbol;
        else
            this.symbol_ = null;
        this.parent_ = parent;
        this.prevItem_ = prevItem;
        this.subItem_ = subItem;
    }

    public bool matches(Item item)
    {
        return item.alternative_ == this.alternative_ && item.index == this.index && item.parent_ == this.parent_;
    }

    public bool isFinal()
    {
        return this.symbol is null;
    }

    public Alternative alternative()
    {
        return this.alternative_;
    }

    public Symbol symbol()
    {
        return this.symbol_;
    }

    public ItemSet parent()
    {
        return this.parent_;
    }

    public Item prevItem()
    {
        return this.prevItem_;
    }

    public Item subItem()
    {
        return this.subItem_;
    }

    public override string toString()
    {
        import std.array : appender;
        import std.conv : to;

        auto writer = appender!string;

        with (this.alternative_)
        {
            writer.put("[ ");
            writer.put(lhs.symbol.toString);
            writer.put(" ->");
            foreach (i; 0 .. this.index)
            {
                writer.put(" ");
                writer.put((cast(SymbolNode) rhs[i]).symbol.toString);
            }
            writer.put(" .");
            foreach (i; this.index .. rhs.length)
            {
                writer.put(" ");
                writer.put((cast(SymbolNode) rhs[i]).symbol.toString);
            }
            writer.put(", ");
            writer.put(this.parent_.index.to!string);
            writer.put(" ]");
        }
        return writer[];
    }
}

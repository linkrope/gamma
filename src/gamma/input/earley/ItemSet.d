module gamma.input.earley.ItemSet;

import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.Nonterminal;
import gamma.grammar.Symbol;
import gamma.input.earley.Item;
import gamma.util.Indexed;

class ItemSet : Indexed
{
    private Item[] items_;

    private size_t index_;

    public static ItemSet initialItemSet(Alternative alternative, Grammar grammar)
    {
        ItemSet itemSet = new ItemSet(0);
        Item item = Item.initialItem(alternative, itemSet);

        itemSet.items_ ~= item;
        itemSet.closure(grammar);
        return itemSet;
    }

    public static ItemSet nextItemSet(ItemSet prevItemSet, Symbol symbol, Grammar grammar)
    {
        ItemSet itemSet = new ItemSet(prevItemSet.index_ + 1);

        foreach (item; prevItemSet.items_)
            if (item.symbol == symbol)
                itemSet.items_ ~= Item.nextItem(item, null);
        itemSet.closure(grammar);
        return itemSet;
    }

    private this(size_t index)
    {
        this.index_ = index;
    }

    public Item[] items()
    {
        return this.items_;
    }

    public override size_t index() const @nogc nothrow pure @safe
    {
        return this.index_;
    }

    private void closure(Grammar grammar)
    {
        size_t length;

        // TODO: repetition only for self referential final items

        do
        {
            length = this.items_.length;
            for (int i = 0; i < this.items_.length; ++i)
            {
                Item item = this.items_[i];

                if (item.isFinal)
                {
                    Symbol lhsSymbol = item.alternative.lhs.symbol;
                    ItemSet parent = item.parent;

                    for (int j = 0; j < parent.items_.length; ++j)
                    {
                        Item parentItem = parent.items_[j];

                        if (parentItem.symbol == lhsSymbol)
                            add(Item.nextItem(parentItem, item));
                    }
                } else if (cast(Nonterminal) item.symbol)
                {
                    Nonterminal nonterminal = cast(Nonterminal) item.symbol;
                    Alternative[] alternatives = grammar.ruleOf(nonterminal).alternatives;

                    foreach (alternative; alternatives)
                        add(Item.initialItem(alternative, this));
                }
            }
        }
        while (this.items_.length > length);
    }

    private void add(Item item)
    {
        // TODO: report ambiguities

        foreach (otherItem; this.items_)
            if (item.matches(otherItem))
                return;
        this.items_ ~= item;
    }

    public override string toString() const
    {
        import std.format : format;

        return format!"{%-(\n\t%s,%)\n}"(this.items_);
    }
}

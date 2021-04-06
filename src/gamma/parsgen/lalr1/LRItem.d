module gamma.parsgen.lalr1.LRItem;

import gamma.grammar.Alternative;
import gamma.grammar.Symbol;
import gamma.grammar.SymbolNode;
import gamma.util.Indexed;

class LRItem : Indexed
{
    const size_t index_;

    Alternative alt;

    const bool altIsInContinuationGrammar;

    const size_t dotPos;

    const bool complete;

    Symbol symbolBehindDot;

    Symbol symbolPrecedingDot;

    LRItem nextItem;

    this(size_t index, Alternative alt, bool altIsInContinuationGrammar, size_t dotPos, LRItem nextItem)
    {
        this.index_ = index;
        this.alt = alt;
        this.altIsInContinuationGrammar = altIsInContinuationGrammar;
        this.dotPos = dotPos;
        this.complete = (dotPos == alt.rhs.length);

        if (!this.complete)
            this.symbolBehindDot = (cast(SymbolNode) alt.rhs[dotPos]).symbol;

        if (dotPos > 0)
            this.symbolPrecedingDot = (cast(SymbolNode) alt.rhs[dotPos - 1]).symbol;

        this.nextItem = nextItem;
    }

    public override string toString()
    {
        import std.array : appender;

        auto writer = appender!string;

        writer.put(this.alt.lhs.symbol.toString);
        if (this.altIsInContinuationGrammar)
            writer.put(" =>");
        else
            writer.put(" ->");
        foreach (i; 0 .. this.dotPos)
        {
            writer.put(' ');
            writer.put((cast(SymbolNode) this.alt.rhs[i]).symbol.toString);
        }
        writer.put(" .");
        foreach (i; this.dotPos .. this.alt.rhs.length)
        {
            writer.put(' ');
            writer.put((cast(SymbolNode) this.alt.rhs[i]).symbol.toString);
        }
        return writer[];
    }

    /**
     * @see gamma.util.Indexed#index()
     */
    public size_t index() const
    {
        return this.index_;
    }
}

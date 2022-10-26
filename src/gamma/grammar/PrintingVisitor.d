module gamma.grammar.PrintingVisitor;

import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.Rule;
import gamma.grammar.SymbolNode;
import gamma.grammar.Visitor;
import std.range;

version (unittest) import gamma.grammar.GrammarBuilder;

public string toPrettyString(Grammar grammar)
{
    import std.array : appender;

    auto writer = appender!string;
    auto visitor = printingVisitor(writer);

    visitor.visit(grammar);
    return writer[];
}

public auto printingVisitor(Writer)(Writer writer)
out (visitor; visitor !is null)
{
    return new PrintingVisitor!Writer(writer);
}

private class PrintingVisitor(Writer) : Visitor
{
    private Writer writer;

    public this(Writer writer)
    {
        this.writer = writer;
    }

    public void visit(Grammar grammar)
    {
        foreach (i, rule; grammar.rules.enumerate)
        {
            if (i > 0)
                this.writer.put("\n");
            rule.accept(this);
        }
    }

    public void visit(Alternative alternative)
    {
        foreach (i, node; alternative.rhs.enumerate)
        {
            if (i > 0)
                this.writer.put(" ");
            node.accept(this);
        }
    }

    public void visit(SymbolNode symbolNode)
    {
        this.writer.put(symbolNode.symbol.toString);
    }

    public void visit(Rule rule)
    {
        rule.alternatives.front.lhs.accept(this);
        this.writer.put(" =");
        foreach (i, alternative; rule.alternatives.enumerate)
        {
            if (i == 0)
            {
                if (!alternative.rhs.empty)
                    this.writer.put("\n    ");
            }
            else
            {
                if (!alternative.rhs.empty)
                    this.writer.put("\n  | ");
                else
                    this.writer.put("\n  |");
            }
            alternative.accept(this);
        }
        if (!rule.alternatives.back.rhs.empty)
            this.writer.put(".\n");
        else
            this.writer.put(" .\n");
    }
}

@("pretty printing")
unittest
{
    import std.string : outdent, stripLeft;

    with (TestGrammarBuilder())
    {
        rule("A: A |");
        rule("B: | B");

        const expected = `
            A =
                A
              | .

            B =
              | B.
            `.outdent.stripLeft;

        assert(grammar.toPrettyString == expected);
    }
}

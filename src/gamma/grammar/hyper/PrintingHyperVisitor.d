module gamma.grammar.hyper.PrintingHyperVisitor;

import gamma.grammar.affixes.Composite;
import gamma.grammar.affixes.Term;
import gamma.grammar.affixes.Variable;
import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.hyper.Group;
import gamma.grammar.hyper.HyperGrammar;
import gamma.grammar.hyper.HyperVisitor;
import gamma.grammar.hyper.Option;
import gamma.grammar.hyper.Repetition;
import gamma.grammar.hyper.RepetitionAlternative;
import gamma.grammar.Node;
import gamma.grammar.Nonterminal;
import gamma.grammar.Rule;
import gamma.grammar.SymbolNode;
import std.range;

version (unittest) import gamma.grammar.GrammarBuilder;

public string toPrettyString(Grammar grammar)
{
    import std.array : appender;

    auto writer = appender!string;
    auto visitor = printingHyperVisitor(writer);

    visitor.visit(grammar);
    return writer[];
}

public string toPrettyString(HyperGrammar hyperGrammar)
{
    import std.array : appender;

    auto writer = appender!string;
    auto visitor = printingHyperVisitor(writer, hyperGrammar.terms);

    visitor.visit(hyperGrammar.grammar);
    return writer[];
}

public auto printingHyperVisitor(Writer)(Writer writer, Term[][] termsByKey = null)
out (visitor; visitor !is null)
{
    return new PrintingHyperVisitor!Writer(writer, termsByKey);
}

private class PrintingHyperVisitor(Writer) : HyperVisitor
{
    private Writer writer;

    private string indentation;

    private Term[][] termsByKey;

    public this(Writer writer, Term[][] termsByKey)
    {
        this.writer = writer;
        this.termsByKey = termsByKey;
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
            {
                this.writer.put("\n");
                this.writer.put(this.indentation);
            }
            node.accept(this);
        }
    }

    public void visit(SymbolNode symbolNode)
    {
        import gamma.grammar.hyper.HyperSymbolNode : HyperSymbolNode;

        this.writer.put(symbolNode.symbol.toString);
        if (cast(HyperSymbolNode) symbolNode)
        {
            auto hyperSymbolNode = cast(HyperSymbolNode) symbolNode;

            if (hyperSymbolNode.params !is null)
            {

                const key = hyperSymbolNode.params.key;
                auto terms = (key < this.termsByKey.length) ? this.termsByKey[key] : null;

                this.writer.put(" <");
                foreach (i, term; terms.enumerate)
                {
                    if (i > 0)
                        this.writer.put(", ");
                    this.writer.write(term);
                }
                this.writer.put(">");
            }
        }
    }

    public void visit(Rule rule)
    {
        Alternative alternative = rule.alternatives.front;

        alternative.lhs.accept(this);
        this.writer.put(":");
        this.indentation = null;
        printHyperExpr(rule.alternatives);
        if (!rule.alternatives.back.rhs.empty)
            this.writer.put(".\n");
        else
            this.writer.put(" .\n");
    }

    public void visit(Group group)
    {
        this.writer.put("(");
        printHyperExpr(group.rule.alternatives);
        this.writer.put("\n");
        this.writer.put(this.indentation);
        this.writer.put(")");
    }

    public void visit(Option option)
    {
        this.writer.put("[");
        printHyperExpr(option.rule.alternatives);
        this.writer.put("\n");
        this.writer.put(this.indentation);
        this.writer.put("]");
    }

    public void visit(Repetition repetition)
    {
        this.writer.put("{");
        printHyperExpr(repetition.rule.alternatives);
        this.writer.put("\n");
        this.writer.put(this.indentation);
        this.writer.put("}");
    }

    public void visit(RepetitionAlternative alternative)
    {
        visit(cast(Alternative) alternative);
    }

    private void printHyperExpr(Alternative[] alternatives)
    {
        const indentation = this.indentation;

        scope (exit)
            this.indentation = indentation;

        this.indentation ~= "    ";
        foreach (i, alternative; alternatives.enumerate)
        {
            if (i == 0)
            {
                if (!alternative.rhs.empty)
                {
                    this.writer.put("\n");
                    this.writer.put(this.indentation);
                }
            }
            else
            {
                this.writer.put("\n");
                this.writer.put(indentation);
                if (!alternative.rhs.empty)
                    this.writer.put("  | ");
                else
                    this.writer.put("  |");
            }
            alternative.accept(this);
        }
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
            A:
                A
              | .

            B:
              | B.
            `.outdent.stripLeft;

        assert(grammar.toPrettyString == expected);
    }
}

private void write(Writer)(Writer writer, Term term)
{
    if (auto variable = cast(Variable) term)
    {
        writer.write(variable);
    }
    else if (auto composite = cast(Composite) term)
    {
        auto terms = composite.terms;

        foreach (i, node; composite.alternative.rhs.enumerate)
        {
            if (i > 0)
                writer.put(" ");

            SymbolNode symbolNode = cast(SymbolNode) node;

            if (cast(Nonterminal) symbolNode.symbol)
            {
                writer.write(terms.front);
                terms.popFront;
            }
            else
            {
                writer.put(symbolNode.symbol.toString);
            }
        }
    }
}

private void write(Writer)(Writer writer, Variable variable)
{
    import std.conv : to;

    if (variable.unequal)
        writer.put("!");
    writer.put(variable.nonterminal.toString);
    if (!variable.number.isNull)
        writer.put(variable.number.get.to!string);
}

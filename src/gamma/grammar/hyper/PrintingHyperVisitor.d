module gamma.grammar.hyper.PrintingHyperVisitor;

import gamma.grammar.affixes.Variable;
import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.hyper.ActualParams;
import gamma.grammar.hyper.Group;
import gamma.grammar.hyper.HyperAlternative;
import gamma.grammar.hyper.HyperVisitor;
import gamma.grammar.hyper.Option;
import gamma.grammar.hyper.Params;
import gamma.grammar.hyper.Repetition;
import gamma.grammar.Node;
import gamma.grammar.Rule;
import gamma.grammar.SymbolNode;
import gamma.input.earley.AffixForm;
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

public auto printingHyperVisitor(Writer)(Writer writer)
out (visitor; visitor !is null)
{
    return new PrintingHyperVisitor!Writer(writer);
}

private class PrintingHyperVisitor(Writer) : HyperVisitor
{
    private Writer writer;

    private string indentation;

    public this(Writer writer)
    {
        this.writer = writer;
    }

    public void visit(Grammar grammar)
    {
        import std.algorithm : each;

        grammar.rules.each!(rule => rule.accept(this));
    }

    public void visit(Rule rule)
    {
        foreach (alternative; rule.alternatives)
        {
            alternative.lhs.accept(this);
            this.writer.put(":");
            this.indentation = "    ";
            alternative.accept(this);
            if (alternative.rhs.empty)
            {
                this.writer.put("\n");
                this.writer.put(this.indentation);
            }
            this.writer.put(".\n");
        }
    }

    public void visit(Alternative alternative)
    {
        if (auto hyperAlternative = cast(HyperAlternative) alternative)
        {
            visit(hyperAlternative);
            return;
        }

        foreach (node; alternative.rhs)
        {
            this.writer.put("\n");
            this.writer.put(this.indentation);
            node.accept(this);
        }
    }

    public void visit(HyperAlternative alternative)
    {
        if (alternative.params !is null)
        {
            this.writer.put(" ");
            this.writer.write(alternative.params);
        }

        foreach (node; alternative.rhs)
        {
            this.writer.put("\n");
            this.writer.put(this.indentation);
            node.accept(this);
        }
    }

    public void visit(SymbolNode symbolNode)
    {
        this.writer.put(symbolNode.symbol.toString);
    }

    public void visit(ActualParams actualParams)
    {
        this.writer.write(actualParams.params);
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
        if (option.endParams !is null)
        {
            this.writer.put(" ");
            this.writer.write(option.endParams);
        }
    }

    public void visit(Repetition repetition)
    {
        this.writer.put("{");
        printHyperExpr(repetition.rule.alternatives);
        this.writer.put("\n");
        this.writer.put(this.indentation);
        this.writer.put("}");
        if (repetition.endParams !is null)
        {
            this.writer.put(" ");
            this.writer.write(repetition.endParams);
        }
    }

    private void printHyperExpr(Alternative[] alternatives)
    {
        const indentation = this.indentation;

        scope (exit)
            this.indentation = indentation;

        this.indentation ~= "    ";
        foreach (i, alternative; alternatives.enumerate)
        {
            if (i > 0)
            {
                this.writer.put("\n");
                this.writer.put(indentation);
                this.writer.put("|");
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
                A.
            A:
                .
            B:
                .
            B:
                B.
            `.outdent.stripLeft;

        assert(grammar.toPrettyString == expected);
    }
}

private void write(Writer)(Writer writer, Params params)
in (params !is null)
{
    writer.put("<");
    foreach (i, affixForm; params.affixForms.enumerate)
    {
        if (i > 0)
            writer.put(", ");
        writer.write(affixForm);
    }
    writer.put(">");
}

private void write(Writer)(Writer writer, AffixForm affixForm)
{
    import gamma.grammar.Nonterminal : Nonterminal;

    auto variables = affixForm.variables;

    foreach (i, symbolNode; affixForm.symbolNodes.enumerate)
    {
        if (i > 0)
            writer.put(" ");
        if (cast(Nonterminal) symbolNode.symbol)
        {
            assert(!variables.empty);

            writer.write(variables.front);
            variables.popFront;
        }
        else
        {
            writer.put(symbolNode.symbol.toString);
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

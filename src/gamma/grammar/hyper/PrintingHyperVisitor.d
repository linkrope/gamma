module gamma.grammar.hyper.PrintingHyperVisitor;

import gamma.grammar.affixes.Composite;
import gamma.grammar.affixes.Direction;
import gamma.grammar.affixes.Signature;
import gamma.grammar.affixes.Term;
import gamma.grammar.affixes.Variable;
import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.hyper.Group;
import gamma.grammar.hyper.HyperGrammar;
import gamma.grammar.hyper.HyperVisitor;
import gamma.grammar.hyper.Option;
import gamma.grammar.hyper.Params;
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
    auto visitor = printingHyperVisitor(writer, hyperGrammar.terms, hyperGrammar.signaturesByKey);

    visitor.visit(hyperGrammar.grammar);
    return writer[];
}

public auto printingHyperVisitor(Writer)(Writer writer, Term[][] termsByKey = null, Signature[] signaturesByKey = null)
out (visitor; visitor !is null)
{
    return new PrintingHyperVisitor!Writer(writer, termsByKey, signaturesByKey);
}

private class PrintingHyperVisitor(Writer) : HyperVisitor
{
    private Writer writer;

    private string indentation;

    private Term[][] termsByKey;

    private Signature[] signaturesByKey;

    public this(Writer writer, Term[][] termsByKey, Signature[] signaturesByKey)
    {
        this.writer = writer;
        this.termsByKey = termsByKey;
        this.signaturesByKey = signaturesByKey;
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
        import gamma.grammar.hyper.HyperLhsNode : HyperLhsNode;

        if (auto lhs = cast(HyperLhsNode) alternative.lhs)
            if (lhs.params !is null)
            {
                printParams(lhs.params);
                if (!alternative.rhs.empty)
                    this.writer.put(" ");
            }
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
        if (auto hyperSymbolNode = cast(HyperSymbolNode) symbolNode)
            if (hyperSymbolNode.params !is null)
            {
                this.writer.put(" ");
                printParams(hyperSymbolNode.params);
            }
    }

    public void visit(Rule rule)
    {
        import gamma.grammar.hyper.HyperLhsNode : HyperLhsNode;

        const name = rule.alternatives.front.lhs.nonterminal.toString;

        foreach (alternative; rule.alternatives)
        {
            auto lhs = cast(HyperLhsNode) alternative.lhs;

            this.writer.put(name);
            if (lhs !is null && lhs.params !is null)
            {
                this.writer.put(" ");
                printParams(lhs.params);
            }
            this.writer.put(":");
            this.indentation = null;
            printSingleAlternativeBody(alternative);
        }
    }

    private void printSingleAlternativeBody(Alternative alternative)
    {
        import gamma.grammar.hyper.HyperSymbolNode : HyperSymbolNode;

        // suppress the lhs params — already printed before the colon
        const indentation = this.indentation;

        scope (exit)
            this.indentation = indentation;

        this.indentation ~= "    ";
        if (!alternative.rhs.empty)
        {
            this.writer.put("\n");
            this.writer.put(this.indentation);
            foreach (i, node; alternative.rhs.enumerate)
            {
                if (i > 0)
                {
                    this.writer.put("\n");
                    this.writer.put(this.indentation);
                }
                node.accept(this);
            }
            this.writer.put(".\n");
        }
        else
        {
            this.writer.put(" .\n");
        }
    }

    public void visit(Group group)
    {
        if (group.params !is null)
        {
            printParams(group.params);
            this.writer.put(" ");
        }
        this.writer.put("(");
        printHyperExpr(group.rule.alternatives);
        this.writer.put("\n");
        this.writer.put(this.indentation);
        this.writer.put(")");
    }

    public void visit(Option option)
    {
        if (option.params !is null)
        {
            printParams(option.params);
            this.writer.put(" ");
        }
        this.writer.put("[");
        printHyperExpr(option.rule.alternatives);
        this.writer.put("\n");
        this.writer.put(this.indentation);
        this.writer.put("]");
        if (option.endParams !is null)
        {
            this.writer.put(" ");
            printParams(option.endParams);
        }
    }

    public void visit(Repetition repetition)
    {
        if (repetition.params !is null)
        {
            printParams(repetition.params);
            this.writer.put(" ");
        }
        this.writer.put("{");
        printHyperExpr(repetition.rule.alternatives);
        this.writer.put("\n");
        this.writer.put(this.indentation);
        this.writer.put("}");
        if (repetition.endParams !is null)
        {
            this.writer.put(" ");
            printParams(repetition.endParams);
        }
    }

    public void visit(RepetitionAlternative alternative)
    {
        visit(cast(Alternative) alternative);
        if (alternative.params !is null)
        {
            this.writer.put(" ");
            printParams(alternative.params);
        }
    }

    private void printParams(Params params)
    {
        const key = params.key;
        auto terms = (key < this.termsByKey.length) ? this.termsByKey[key] : null;
        auto signature = (key < this.signaturesByKey.length) ? this.signaturesByKey[key] : null;

        this.writer.put("<");
        foreach (i, term; terms.enumerate)
        {
            if (i > 0)
                this.writer.put(", ");
            if (signature !is null)
            {
                this.writer.put((signature.direction[i] == Direction.input) ? "-" : "+");
                this.writer.put(" ");
                this.writer.write(term);
                this.writer.put(": ");
                this.writer.put(signature.domains[i].toString);
            }
            else
            {
                this.writer.write(term);
            }
        }
        this.writer.put(">");
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
                if (alternative.hasContent)
                {
                    this.writer.put("\n");
                    this.writer.put(this.indentation);
                }
            }
            else
            {
                this.writer.put("\n");
                this.writer.put(indentation);
                if (alternative.hasContent)
                    this.writer.put("  | ");
                else
                    this.writer.put("  |");
            }
            alternative.accept(this);
        }
    }
}

private bool hasContent(Alternative alternative)
{
    import gamma.grammar.hyper.HyperLhsNode : HyperLhsNode;

    if (!alternative.rhs.empty)
        return true;
    if (auto lhs = cast(HyperLhsNode) alternative.lhs)
        if (lhs.params !is null)
            return true;
    if (auto repetitionAlternative = cast(RepetitionAlternative) alternative)
        if (repetitionAlternative.params !is null)
            return true;
    return false;
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
            A: .

            B: .
            B:
                B.
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

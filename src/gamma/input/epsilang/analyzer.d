module gamma.input.epsilang.analyzer;

import gamma.grammar.Grammar;
import gamma.grammar.GrammarProperties;
import gamma.input.epsilang.parser;
import io;
import log;
import std.stdio;

class Analyzer
{
    private bool verbose;

    private Parser parser;

    private Grammar metaGrammar;

    private Grammar hyperGrammar;

    public this(bool verbose)
    {
        this.verbose = verbose;
    }

    public void analyze(Input input)
    {
        import gamma.grammar.hyper.EBNFConverter : convert;
        import std.exception : enforce;

        this.parser = new Parser(input);
        this.parser.parseSpecification;

        enforce(this.parser.getErrorCount == 0);

        this.metaGrammar = this.parser.yieldMetaGrammar;
        if (this.metaGrammar && this.verbose)
        {
            import gamma.grammar.PrintingVisitor : printingVisitor;

            auto visitor = printingVisitor(stdout.lockingTextWriter);

            visitor.visit(this.metaGrammar);
            stdout.writeln;
        }

        auto hyperEBNFGrammar = parser.yieldHyperGrammar;

        if (hyperEBNFGrammar && this.verbose)
        {
            import gamma.grammar.hyper.PrintingHyperVisitor : printingHyperVisitor;

            auto visitor = printingHyperVisitor(stdout.lockingTextWriter);

            visitor.visit(hyperEBNFGrammar);
            stdout.writeln;
        }

        enforce(this.metaGrammar && hyperEBNFGrammar,
            "grammar not well defined");

        this.hyperGrammar = convert(hyperEBNFGrammar);
        if (this.verbose)
        {
            import gamma.grammar.hyper.PrintingHyperVisitor : printingHyperVisitor;

            auto visitor = printingHyperVisitor(stdout.lockingTextWriter);

            visitor.visit(this.hyperGrammar);
            stdout.writeln;
        }

        auto grammarProperties = new GrammarProperties(this.hyperGrammar);

        if (grammarProperties.isReduced)
        {
            trace!"hyper grammar is reduced";
        }
        if (!grammarProperties.isProductive(this.hyperGrammar.startSymbol))
        {
            error!"start symbol %s is unproductive"(this.hyperGrammar.startSymbol);

            enforce(false);
        }
    }

    public Grammar parserGrammar()
    {
        import gamma.grammar.hyper.EBNFConverter : convert;
        import gamma.grammar.Node : Node;
        import gamma.grammar.Symbol : Symbol;
        import gamma.parsgen.lalr1.ParserGrammarBuilder : extendedCfgFromHyperGrammar;
        import gamma.parsgen.lalr1.PredicateFilter : PredicateFilter;
        import std.algorithm : map;
        import std.array : assocArray;
        import std.typecons : tuple;

        bool[Symbol] lexicalHyperNonterminals = this.parser.getLexicalHyperNonterminals.byKeyValue
            .map!(pair => tuple(cast(Symbol) pair.key, pair.value))
            .assocArray;
        auto predicateFilter = new class PredicateFilter
        {
            override bool isPredicate(Node node)
            {
                return false;
            }
        };
        auto parserGrammar = this.hyperGrammar
            .convert
            .extendedCfgFromHyperGrammar(lexicalHyperNonterminals, predicateFilter);

        if (this.verbose)
        {
            import gamma.grammar.hyper.PrintingHyperVisitor : printingHyperVisitor;

            auto visitor = printingHyperVisitor(stdout.lockingTextWriter);

            visitor.visit(parserGrammar);
            stdout.writeln;
        }
        return parserGrammar;
    }
}

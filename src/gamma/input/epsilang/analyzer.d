module gamma.input.epsilang.analyzer;

import gamma.grammar.Grammar;
import gamma.grammar.GrammarProperties;
import gamma.input.epsilang.parser;
import io;
import log;

class Analyzer
{
    private Parser parser;

    private Grammar metaGrammar;

    private Grammar hyperGrammar;

    public void analyze(Input input)
    {
        import gamma.grammar.hyper.EBNFConverter : convert;
        import std.exception : enforce;

        this.parser = new Parser(input);
        this.parser.parseSpecification;

        enforce(this.parser.getErrorCount == 0);

        this.metaGrammar = this.parser.yieldMetaGrammar;
        if (this.metaGrammar)
        {
            import gamma.grammar.PrintingVisitor : toPrettyString;

            log.trace!"meta grammar:\n%s"(this.metaGrammar.toPrettyString);
        }

        auto hyperEBNFGrammar = parser.yieldHyperGrammar;

        if (hyperEBNFGrammar)
        {
            import gamma.grammar.hyper.PrintingHyperVisitor : toPrettyString;

            log.trace!"hyper grammar:\n%s"(hyperEBNFGrammar.toPrettyString);
        }

        enforce(this.metaGrammar && hyperEBNFGrammar,
            "grammar not well defined");

        this.hyperGrammar = convert(hyperEBNFGrammar);
        // TODO
        {
            import gamma.grammar.hyper.PrintingHyperVisitor : toPrettyString;

            log.trace!"converted hyper grammar:\n%s"(this.hyperGrammar.toPrettyString);
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

        // TODO
        {
            import gamma.grammar.PrintingVisitor : toPrettyString;

            trace!"parser grammar:\n%s"(parserGrammar.toPrettyString);
        }
        return parserGrammar;
    }
}

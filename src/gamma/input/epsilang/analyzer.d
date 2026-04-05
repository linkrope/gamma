module gamma.input.epsilang.analyzer;

import gamma.grammar.Grammar;
import gamma.grammar.GrammarProperties;
import gamma.grammar.hyper.HyperGrammar;
import gamma.input.epsilang.parser;
import io;
import log;

class Analyzer
{
    private Parser parser;

    private HyperGrammar plainHyperGrammar_;

    private GrammarProperties hyperGrammarProperties;

    public void analyze(Input input)
    {
        import gamma.grammar.hyper.EBNFConverter : convert;
        import std.exception : enforce;

        this.parser = new Parser(input);
        this.parser.parseSpecification;

        enforce(this.parser.getErrorCount == 0);

        auto metaGrammar = this.parser.buildMetaGrammar;

        if (metaGrammar)
        {
            import gamma.grammar.PrintingVisitor : toPrettyString;

            log.trace!"meta grammar:\n%s"(metaGrammar.toPrettyString);
        }

        auto hyperEBNFGrammar = parser.buildHyperGrammar;

        if (hyperEBNFGrammar)
        {
            import gamma.grammar.hyper.PrintingHyperVisitor : toPrettyString;

            log.trace!"hyper grammar:\n%s"(hyperEBNFGrammar.toPrettyString);
        }

        enforce(metaGrammar && hyperEBNFGrammar,
            "grammar not well defined");

        if (hyperEBNFGrammar.grammar.isPlain)
        {
            this.plainHyperGrammar_ = hyperEBNFGrammar;
        }
        else
        {
            import gamma.grammar.hyper.PrintingHyperVisitor : toPrettyString;

            this.plainHyperGrammar_ = new HyperGrammar(convert(hyperEBNFGrammar.grammar), hyperEBNFGrammar.terms);
            log.trace!"converted hyper grammar:\n%s"(this.plainHyperGrammar_.toPrettyString);
        }

        this.hyperGrammarProperties = new GrammarProperties(this.plainHyperGrammar_.grammar, this.parser.getLexicalHyperNonterminals);
        if (this.hyperGrammarProperties.isReduced)
        {
            trace!"hyper grammar is reduced";
        }
        if (!this.hyperGrammarProperties.isProductive(this.plainHyperGrammar_.grammar.startSymbol))
        {
            error!"start symbol %s is unproductive"(this.plainHyperGrammar_.grammar.startSymbol);

            enforce(false);
        }
        foreach (nonterminal; this.plainHyperGrammar_.grammar.nonterminals)
            if (!this.hyperGrammarProperties.isProductive(nonterminal))
            {
                import gamma.grammar.hyper.AnonymousNonterminal : AnonymousNonterminal;

                const position = this.plainHyperGrammar_.grammar.ruleOf(nonterminal).lhs.position;

                if (cast(AnonymousNonterminal) nonterminal)
                    warn!"EBNF expression is unproductive\n%s"(position);
                else
                    warn!"%s is unproductive\n%s"(nonterminal, position);
            }
        foreach (nonterminal; this.plainHyperGrammar_.grammar.nonterminals)
            if (!this.hyperGrammarProperties.isReachable(nonterminal))
            {
                import gamma.grammar.hyper.AnonymousNonterminal : AnonymousNonterminal;

                const position = this.plainHyperGrammar_.grammar.ruleOf(nonterminal).lhs.position;

                if (!cast(AnonymousNonterminal) nonterminal)
                    warn!"%s is unreachable\n%s"(nonterminal, position);
            }
    }

    public HyperGrammar plainHyperGrammar()
    {
        return this.plainHyperGrammar_;
    }

    public Grammar parserGrammar()
    {
        import gamma.grammar.Nonterminal : Nonterminal;
        import gamma.grammar.Symbol : Symbol;
        import gamma.parsgen.lalr1.ParserGrammarBuilder : toExtendedParserGrammar;

        bool isTerminal(Symbol symbol)
        {
            return this.hyperGrammarProperties.isLexicalNonterminal(symbol);
        }

        bool isPredicate(Symbol symbol)
        {
            // bad things happen when the start symbol is taken as a predicate
            return symbol != this.plainHyperGrammar_.grammar.startSymbol
                && this.hyperGrammarProperties.isStrongNullable(symbol);
        }

        auto parserGrammar = this.plainHyperGrammar_.grammar
            .toExtendedParserGrammar(&isTerminal, &isPredicate);

        // TODO
        {
            import gamma.grammar.PrintingVisitor : toPrettyString;

            trace!"parser grammar:\n%s"(parserGrammar.toPrettyString);
        }
        return parserGrammar;
    }
}

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

    private GrammarProperties hyperGrammarProperties;

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

        if (hyperEBNFGrammar.isPlain)
        {
            this.hyperGrammar = hyperEBNFGrammar;
        }
        else
        {
            import gamma.grammar.hyper.PrintingHyperVisitor : toPrettyString;

            this.hyperGrammar = convert(hyperEBNFGrammar);
            log.trace!"converted hyper grammar:\n%s"(this.hyperGrammar.toPrettyString);
        }

        this.hyperGrammarProperties = new GrammarProperties(this.hyperGrammar, this.parser.getLexicalHyperNonterminals);
        if (this.hyperGrammarProperties.isReduced)
        {
            trace!"hyper grammar is reduced";
        }
        if (!this.hyperGrammarProperties.isProductive(this.hyperGrammar.startSymbol))
        {
            error!"start symbol %s is unproductive"(this.hyperGrammar.startSymbol);

            enforce(false);
        }
        foreach (nonterminal; this.hyperGrammar.nonterminals)
            if (!this.hyperGrammarProperties.isProductive(nonterminal))
            {
                import gamma.grammar.hyper.AnonymousNonterminal : AnonymousNonterminal;

                const position = this.hyperGrammar.ruleOf(nonterminal).lhs.position;

                if (cast(AnonymousNonterminal) nonterminal)
                    warn!"EBNF expression is unproductive\n%s"(position);
                else
                    warn!"%s is unproductive\n%s"(nonterminal, position);
            }
        foreach (nonterminal; this.hyperGrammar.nonterminals)
            if (!this.hyperGrammarProperties.isReachable(nonterminal))
            {
                import gamma.grammar.hyper.AnonymousNonterminal : AnonymousNonterminal;

                const position = this.hyperGrammar.ruleOf(nonterminal).lhs.position;

                if (!cast(AnonymousNonterminal) nonterminal)
                    warn!"%s is unreachable\n%s"(nonterminal, position);
            }
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
            return symbol != this.hyperGrammar.startSymbol
                && this.hyperGrammarProperties.isStrongNullable(symbol);
        }

        auto parserGrammar = this.hyperGrammar
            .toExtendedParserGrammar(&isTerminal, &isPredicate);

        // TODO
        {
            import gamma.grammar.PrintingVisitor : toPrettyString;

            trace!"parser grammar:\n%s"(parserGrammar.toPrettyString);
        }
        return parserGrammar;
    }
}

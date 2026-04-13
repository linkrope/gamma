module gamma.input.epsilang.analyzer;

import gamma.grammar.Grammar;
import gamma.grammar.GrammarProperties;
import gamma.grammar.hyper.HyperGrammar;
import gamma.grammar.Nonterminal;
import gamma.input.epsilang.parser;
import io;
import log;

struct EAG
{
    Grammar metaGrammar;

    HyperGrammar hyperEBNFGrammar;

    HyperGrammar plainHyperGrammar;

    bool[Nonterminal] lexicalMetaNonterminals;

    bool[Nonterminal] lexicalHyperNonterminals;
}

class Analyzer
{
    private Parser parser;

    private HyperGrammar plainHyperGrammar_;

    private GrammarProperties hyperGrammarProperties;

    public EAG analyze(Input input)
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

        if (hyperEBNFGrammar.isPlain)
        {
            this.plainHyperGrammar_ = hyperEBNFGrammar;
        }
        else
        {
            import gamma.grammar.hyper.PrintingHyperVisitor : toPrettyString;

            this.plainHyperGrammar_ = new HyperGrammar(convert(hyperEBNFGrammar), hyperEBNFGrammar.terms);
            log.trace!"transformed BNF grammar:\n%s"(this.plainHyperGrammar_.toPrettyString);
        }

        this.hyperGrammarProperties =
            new GrammarProperties(this.plainHyperGrammar_, this.parser.getLexicalHyperNonterminals);
        if (this.hyperGrammarProperties.isReduced)
        {
            trace!"hyper grammar is reduced";
        }
        if (!this.hyperGrammarProperties.isProductive(this.plainHyperGrammar_.startSymbol))
        {
            error!"start symbol %s is unproductive"(this.plainHyperGrammar_.startSymbol);

            enforce(false);
        }
        checkStartSymbolSignature;
        foreach (nonterminal; this.plainHyperGrammar_.nonterminals)
            if (!this.hyperGrammarProperties.isProductive(nonterminal))
            {
                import gamma.grammar.hyper.AnonymousNonterminal : AnonymousNonterminal;

                const position = this.plainHyperGrammar_.ruleOf(nonterminal).lhs.position;

                if (cast(AnonymousNonterminal) nonterminal)
                    warn!"EBNF expression is unproductive\n%s"(position);
                else
                    warn!"%s is unproductive\n%s"(nonterminal, position);
            }
        foreach (nonterminal; this.plainHyperGrammar_.nonterminals)
            if (!this.hyperGrammarProperties.isReachable(nonterminal))
            {
                import gamma.grammar.hyper.AnonymousNonterminal : AnonymousNonterminal;

                const position = this.plainHyperGrammar_.ruleOf(nonterminal).lhs.position;

                if (!cast(AnonymousNonterminal) nonterminal)
                    warn!"%s is unreachable\n%s"(nonterminal, position);
            }

        return EAG(metaGrammar, hyperEBNFGrammar, this.plainHyperGrammar_,
            this.parser.getLexicalMetaNonterminals, this.parser.getLexicalHyperNonterminals);
    }

    private void checkStartSymbolSignature()
    {
        import gamma.grammar.affixes.Direction : Direction;
        import gamma.grammar.affixes.Signature : Signature;
        import gamma.grammar.hyper.HyperLhsNode : HyperLhsNode;
        import gamma.grammar.Nonterminal : Nonterminal;
        import std.exception : enforce;
        import std.range : front;

        Nonterminal startSymbol = this.plainHyperGrammar_.startSymbol;
        auto startLhs = cast(HyperLhsNode) this.plainHyperGrammar_.ruleOf(startSymbol).lhs;
        Signature signature = startLhs ? startLhs.signature : null;

        if (signature is null || signature.length != 1 || signature.direction.front != Direction.output)
        {
            error!"start symbol %s must have exactly one output affix\n%s"(startSymbol,
                signature ? signature.position : startLhs ? startLhs.position : UndefPos);

            enforce(false);
        }
    }

    public Grammar parserGrammar()
    {
        import gamma.grammar.Symbol : Symbol;
        import gamma.parsgen.lalr1.ParserGrammarBuilder : toExtendedParserGrammar;

        bool isTerminal(Symbol symbol)
        {
            return this.hyperGrammarProperties.isLexicalNonterminal(symbol);
        }

        bool isPredicate(Symbol symbol)
        {
            // bad things happen when the start symbol is taken as a predicate
            return symbol != this.plainHyperGrammar_.startSymbol
                && this.hyperGrammarProperties.isStrongNullable(symbol);
        }

        auto parserGrammar = this.plainHyperGrammar_
            .toExtendedParserGrammar(&isTerminal, &isPredicate);

        // TODO
        {
            import gamma.grammar.PrintingVisitor : toPrettyString;

            trace!"parser grammar:\n%s"(parserGrammar.toPrettyString);
        }
        return parserGrammar;
    }
}

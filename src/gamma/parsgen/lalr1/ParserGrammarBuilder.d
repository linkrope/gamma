module gamma.parsgen.lalr1.ParserGrammarBuilder;

import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.GrammarBuilder;
import gamma.grammar.GrammarProperties;
import gamma.grammar.LhsNode;
import gamma.grammar.Node;
import gamma.grammar.Nonterminal;
import gamma.grammar.Rule;
import gamma.grammar.Symbol;
import gamma.grammar.SymbolNode;
import gamma.grammar.Terminal;
import gamma.input.epsilang.analyzer : EAG;
import gamma.util.Position;
import log;

/**
 * A compact parser grammar with mappings
 * from its terminals and nonterminals to their original counterparts.
 */
public struct ParserGrammar
{
    Grammar grammar;

    Terminal[Terminal] terminals;

    Nonterminal[Nonterminal] nonterminals;
}

public ParserGrammar toParserGrammar(EAG eag)
{
    import gamma.grammar.PrintingVisitor : toPrettyString;

    auto hyperGrammarProperties = new GrammarProperties(eag.plainHyperGrammar,
        eag.lexicalHyperNonterminals);

    bool isTerminal(Symbol symbol)
    {
        return hyperGrammarProperties.isLexicalNonterminal(symbol);
    }

    bool isPredicate(Symbol symbol)
    {
        return symbol != eag.plainHyperGrammar.startSymbol
            && hyperGrammarProperties.isStrongNullable(symbol);
    }

    auto parserGrammar = eag.plainHyperGrammar
        .toExtendedParserGrammar(&isTerminal, &isPredicate);

    trace!"parser grammar:\n%s"(parserGrammar.grammar.toPrettyString);
    return parserGrammar;
}

public ParserGrammar toExtendedParserGrammar(Grammar grammar,
    bool delegate(Symbol) isTerminal,
    bool delegate(Symbol) isPredicate)
in (grammar.isPlain)
{
    GrammarBuilder grammarBuilder;
    Terminal[Terminal] terminals;
    Nonterminal[Nonterminal] nonterminals;

    Nonterminal originalStartSymbol = grammarBuilder.buildNonterminal(grammar.startSymbol.toString);
    nonterminals[originalStartSymbol] = grammar.startSymbol;
    Nonterminal extStartSymbol = grammarBuilder.buildNonterminal("(Start)");

    // --- Go ahead with rest of parser generation... ---
    {
        Terminal bottom = grammarBuilder.buildTerminal("(end)");
        Node[] rhs = [new SymbolNode(originalStartSymbol, Position()), new SymbolNode(bottom, Position())];

        grammarBuilder.add(
            new Alternative(new LhsNode(extStartSymbol, Position()), rhs, Position()));
    }

    // Filter the pure parser grammar out of the grammar using
    // - help which nonterminal symbols are "lexical nonterminals"
    // - help which RHS symbol occurrences are "predicates"
    // Any alternative/rule the LHS of which is not a nonterminal of the parser grammar is skipped.

    // Current restriction: contrary to the rules above, LALR has --p
    // semantics, so marked lexical rules and their occurrences remain parser
    // rules until a conventional lexer recognizes them as tokens.

    // For the remaining RHS's, SymbolNode's are
    // - not copied to the corresponding parser grammar RHS if they represent a "predicate"
    // - copied to the parser grammar as a terminal if they represent a "lexical nonterminal"
    // - copied to the parser grammar as a nonterminal otherwise
    foreach (rule; grammar.rules)
    {
        foreach (alternative; rule.alternatives)
        {
            if (isPredicate(alternative.lhs.nonterminal))
                break;

            Nonterminal lhs = grammarBuilder.buildNonterminal(alternative.lhs.nonterminal.toString);
            Node[] rhs;

            nonterminals[lhs] = alternative.lhs.nonterminal;
            foreach (node; alternative.rhs)
            {
                assert(cast(SymbolNode) node);

                SymbolNode symbolNode = cast(SymbolNode) node;

                if (isPredicate(symbolNode.symbol))
                    continue;

                Symbol symbol;

                if (auto terminal = cast(Terminal) symbolNode.symbol)
                {
                    auto parserTerminal = grammarBuilder.buildTerminal(terminal.toString);

                    symbol = parserTerminal;
                    terminals[parserTerminal] = terminal;
                }
                else
                {
                    auto nonterminal = cast(Nonterminal) symbolNode.symbol;
                    auto parserNonterminal = grammarBuilder.buildNonterminal(nonterminal.toString);

                    symbol = parserNonterminal;
                    nonterminals[parserNonterminal] = nonterminal;
                }
                rhs ~= new SymbolNode(symbol, symbolNode.position);
            }
            grammarBuilder
                .add(new Alternative(new LhsNode(lhs, alternative.lhs.position), rhs, alternative.position));
        }
    }

    return ParserGrammar(grammarBuilder.getGrammar(extStartSymbol), terminals, nonterminals);
}

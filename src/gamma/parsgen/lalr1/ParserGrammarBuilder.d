module gamma.parsgen.lalr1.ParserGrammarBuilder;

import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.GrammarBuilder;
import gamma.grammar.Node;
import gamma.grammar.Nonterminal;
import gamma.grammar.Rule;
import gamma.grammar.Symbol;
import gamma.grammar.SymbolNode;
import gamma.grammar.Terminal;
import gamma.util.Position;

// TODO: by using the grammar builder the indexes of the symbols will be changed
public Grammar toExtendedParserGrammar(Grammar grammar,
    bool delegate(Symbol) isTerminal,
    bool delegate(Symbol) isPredicate)
in (grammar.isPlain)
{
    GrammarBuilder grammarBuilder;
    Symbol originalStartSymbol = grammarBuilder.buildNonterminal(grammar.startSymbol.toString);
    Nonterminal extStartSymbol = grammarBuilder.buildNonterminal("(Start)");

    // --- Go ahead with rest of parser generation... ---
    {
        Terminal bottom = grammarBuilder.buildTerminal("(end)");
        Node[] rhs = [new SymbolNode(originalStartSymbol, Position()), new SymbolNode(bottom, Position())];

        grammarBuilder.add(
            new Alternative(new SymbolNode(extStartSymbol, Position()), rhs, Position()));
    }

    // Filter the pure parser grammar out of the grammar using
    // - help which nonterminal symbols are "lexical nonterminals"
    // - help which RHS symbol occurrences are "predicates"
    // Any alternative/rule the LHS of which is not a nonterminal of the parser grammar is skipped.
    // For the remaining RHS's, SymbolNode's are
    // - not copied to the corresponding parser grammar RHS if they represent a "predicate"
    // - copied to the parser grammar as a terminal if they represent a "lexical nonterminal"
    // - copied to the parser grammar as a nonterminal otherwise
    foreach (rule; grammar.rules)
    {
        foreach (alternative; rule.alternatives)
        {
            if (isTerminal(alternative.lhs.symbol))
                break;
            if (isPredicate(alternative.lhs.symbol))
                break;

            Nonterminal lhs = grammarBuilder.buildNonterminal(alternative.lhs.symbol.toString);
            Node[] rhs;

            foreach (node; alternative.rhs)
            {
                assert(cast(SymbolNode) node);

                SymbolNode symbolNode = cast(SymbolNode) node;

                if (isPredicate(symbolNode.symbol))
                    continue;

                Symbol symbol;

                if (isTerminal(symbolNode.symbol) || cast(Terminal) symbolNode.symbol)
                    symbol = grammarBuilder.buildTerminal(symbolNode.symbol.toString);
                else
                    symbol = grammarBuilder.buildNonterminal(symbolNode.symbol.toString);
                rhs ~= new SymbolNode(symbol, symbolNode.position);
            }
            grammarBuilder
                .add(new Alternative(new SymbolNode(lhs, alternative.lhs.position), rhs, alternative.position));
        }
    }

    return grammarBuilder.getGrammar(extStartSymbol);
}

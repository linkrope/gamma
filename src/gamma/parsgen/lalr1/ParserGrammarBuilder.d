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
public Grammar extendedCfgFromHyperGrammar(Grammar hyperGrammar,
    bool delegate(Symbol) isTerminal,
    bool delegate(Symbol) isPredicate)
{
    auto grammarBuilder = GrammarBuilder();
    Symbol originalStartSymbol = grammarBuilder.buildNonterminal(hyperGrammar.startSymbol.toString);
    Nonterminal extStartSymbol = grammarBuilder.buildNonterminal("(Start)");

    // --- Go ahead with rest of parser generation... ---
    {
        Terminal bottom = grammarBuilder.buildTerminal("(end)");
        Node[] rhs = [new SymbolNode(originalStartSymbol, Position()), new SymbolNode(bottom, Position())];

        grammarBuilder.add(
            new Alternative(new SymbolNode(extStartSymbol, Position()), rhs, Position()));
    }

    // Filter the pure CFG out of the hyperGrammar using
    // - help which nonterminal symbols are "lexical nonterminals"
    // - help which RHS symbol occurrences are "predicates"
    // Any Alternative/Rule the LHS of which is not a Nonterminal of the parser CFG is skipped.
    // For the remaining RHS's, SymbolNode's are
    // - not copied to the corresponding target CFG RHS if they represent a "predicate";
    // - copied to the target CFG as a Terminal if they represent a "lexical nonterminal";
    // - copied to the target CFG as a Nonterminal otherwise.
    foreach (hyperRule; hyperGrammar.rules)
    {
        foreach (hyperAlt; hyperRule.alternatives)
        {
            if (isTerminal(hyperAlt.lhs.symbol))
                break;
            if (isPredicate(hyperAlt.lhs.symbol))
                break;

            Nonterminal lhs = grammarBuilder.buildNonterminal(hyperAlt.lhs.symbol.toString);
            Node[] rhs;

            foreach (rhsNode; hyperAlt.rhs)
            {
                assert(cast(SymbolNode) rhsNode);

                SymbolNode node = cast(SymbolNode) rhsNode;

                if (isPredicate(node.symbol))
                    continue;

                Symbol sym;

                if (isTerminal(node.symbol) || cast(Terminal)(cast(SymbolNode) node).symbol)
                    sym = grammarBuilder.buildTerminal(node.symbol.toString);
                else
                    sym = grammarBuilder.buildNonterminal(node.symbol.toString);
                rhs ~= new SymbolNode(sym, node.position);
            }
            grammarBuilder
                .add(new Alternative(new SymbolNode(lhs, hyperAlt.lhs.position), rhs, hyperAlt.position));
        }
    }

    return grammarBuilder.getGrammar(extStartSymbol);
}

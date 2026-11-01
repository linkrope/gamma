module gamma.parsgen.lalr1.LexerGrammarBuilder;

import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.GrammarBuilder;
import gamma.grammar.LhsNode;
import gamma.grammar.Node;
import gamma.grammar.SymbolNode;
import gamma.grammar.Terminal;
import gamma.input.epsilang.analyzer : EAG;
import gamma.util.Position;
import io : UndefPos;

/**
 * The character grammar used by the EAG lexer.
 * `candidateTerminals` associates a Token alternative with its original
 * Gamma terminal; it deliberately does not use compact parser-table ids.
 */
public struct LexerGrammar
{
    Grammar grammar;

    Terminal[Alternative] candidateTerminals;

    string[] terminalNames;
}

public LexerGrammar toLexerGrammar(EAG eag)
{
    import std.conv : to;
    import std.utf : byDchar;

    GrammarBuilder builder;
    auto positions = eag.terminalPositions;
    auto root = builder.buildNonterminal("(LexStart)");
    auto candidate = builder.buildNonterminal("(Token)");
    auto tokenEnd = builder.buildTerminal("(token-end)");

    builder.add(new Alternative(new LhsNode(root, UndefPos),
        [new SymbolNode(candidate, UndefPos), new SymbolNode(tokenEnd, UndefPos)],
        UndefPos));

    string[] terminalNames;

    terminalNames.length = eag.plainHyperGrammar.terminals.length;

    Terminal[Alternative] candidateTerminals = null;

    foreach (terminal; eag.plainHyperGrammar.terminals)
    {
        const quotedRepresentation = terminal.toString;
        const representation = quotedRepresentation[1 .. $ - 1];

        assert(representation.length != 0, "an empty quoted terminal cannot be a lexer token");

        terminalNames[terminal.index] = quotedRepresentation;

        const Position position = positions.get(terminal, UndefPos);
        Node[] rhs = null;

        foreach (character; representation.byDchar)
        {
            auto characterTerminal = builder.buildTerminal(character.to!string);

            rhs ~= new SymbolNode(characterTerminal, position);
        }

        auto alternative = new Alternative(new LhsNode(candidate, position), rhs, position);

        builder.add(alternative);
        candidateTerminals[alternative] = terminal;
    }

    return LexerGrammar(builder.getGrammar(root), candidateTerminals, terminalNames);
}

private Position[Terminal] terminalPositions(EAG eag)
{
    Position[Terminal] result = null;

    foreach (rule; eag.plainHyperGrammar.rules)
    {
        foreach (alternative; rule.alternatives)
        {
            foreach (node; alternative.rhs)
            {
                auto symbolNode = cast(SymbolNode) node;

                if (symbolNode is null)
                    continue;

                if (auto terminal = cast(Terminal) symbolNode.symbol)
                    if (terminal !in result)
                        result[terminal] = symbolNode.position;
            }
        }
    }
    return result;
}

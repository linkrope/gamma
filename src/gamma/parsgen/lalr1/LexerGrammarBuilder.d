module gamma.parsgen.lalr1.LexerGrammarBuilder;

import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.GrammarBuilder;
import gamma.grammar.GrammarProperties;
import gamma.grammar.LhsNode;
import gamma.grammar.Node;
import gamma.grammar.Nonterminal;
import gamma.grammar.SymbolNode;
import gamma.grammar.Terminal;
import gamma.input.epsilang.analyzer : EAG;
import gamma.runtime.lr.LR1ParserTables : LexerCandidate, LexerRule;
import gamma.util.Position;
import io : UndefPos;
import std.range : empty;
import std.typecons : Flag, No;

/**
 * The character grammar used by the EAG lexer.
 * Its metadata maps reductions back to source terminals and hyper rules,
 * deliberately avoiding compact parser-table IDs.
 */
public struct LexerGrammar
{
    Grammar grammar;

    Terminal tokenEnd;

    Nonterminal[Terminal] helpersByTerminal;

    LexerCandidate[Alternative] candidates;

    LexerRule[Alternative] rules;

    size_t[][Nonterminal] lexicalNonterminalOwners;

    string[] terminalNames;

    string[] nonterminalNames;
}

public LexerGrammar toLexerGrammar(EAG eag,
    Flag!"parsesLexicalNonterminals" parsesLexicalNonterminals = No.parsesLexicalNonterminals)
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

    string[] terminalNames = new string[eag.plainHyperGrammar.terminals.length];
    string[] nonterminalNames = new string[eag.plainHyperGrammar.nonterminals.length];
    LexerCandidate[Alternative] candidates = null;
    LexerRule[Alternative] rules = null;
    size_t[][Nonterminal] lexicalNonterminalOwners = null;
    Nonterminal[Terminal] helpersByTerminal = null;
    Nonterminal[Nonterminal] lexicalNonterminals = null;
    bool[Nonterminal] lexicalRoots = eag.lexicalHyperNonterminals;

    if (parsesLexicalNonterminals)
        lexicalRoots = null;

    auto properties = new GrammarProperties(eag.plainHyperGrammar, lexicalRoots);

    foreach (nonterminal; eag.plainHyperGrammar.nonterminals)
    {
        nonterminalNames[nonterminal.index] = nonterminal.toString;
        if (properties.isLexicalNonterminal(nonterminal))
            lexicalNonterminals[nonterminal] = builder.buildNonterminal(nonterminal.toString);
    }

    void collectLexicalNonterminalOwners(Nonterminal source, size_t owner,
        ref bool[Nonterminal] visited)
    {
        if (source in visited)
            return;

        visited[source] = true;
        lexicalNonterminalOwners[lexicalNonterminals[source]] ~= owner;
        foreach (alternative; eag.plainHyperGrammar.ruleOf(source).alternatives)
            foreach (node; alternative.rhs)
            {
                auto symbolNode = cast(SymbolNode) node;

                assert(symbolNode !is null);

                if (auto nonterminal = cast(Nonterminal) symbolNode.symbol)
                    collectLexicalNonterminalOwners(nonterminal, owner, visited);
            }
    }

    foreach (nonterminal, isLexicalRoot; lexicalRoots)
    {
        if (!isLexicalRoot)
            continue;

        bool[Nonterminal] visited = null;

        collectLexicalNonterminalOwners(nonterminal, nonterminal.index, visited);
    }

    Nonterminal terminalHelper(Terminal terminal)
    {
        if (auto helper = terminal in helpersByTerminal)
            return *helper;

        const quotedRepresentation = terminal.toString;
        const representation = quotedRepresentation[1 .. $ - 1];

        assert(!representation.empty, "an empty quoted terminal cannot be a lexer token");

        const Position position = positions.get(terminal, UndefPos);
        auto helper = builder.buildNonterminal("(Lex " ~ terminal.index.to!string ~ ")");
        Node[] rhs = null;

        foreach (character; representation.byDchar)
        {
            auto characterTerminal = builder.buildTerminal(character.to!string);

            rhs ~= new SymbolNode(characterTerminal, position);
        }

        auto alternative = new Alternative(new LhsNode(helper, position), rhs, position);

        builder.add(alternative);
        helpersByTerminal[terminal] = helper;
        rules[alternative] = LexerRule(size_t.max, size_t.max, terminal.index);
        return helper;
    }

    bool[Terminal] parserTerminals = null;

    foreach (rule; eag.plainHyperGrammar.rules)
    {
        if (properties.isLexicalNonterminal(rule.lhs.nonterminal)
            || properties.isStrongNullable(rule.lhs.nonterminal))
            continue;
        foreach (alternative; rule.alternatives)
            foreach (node; alternative.rhs)
                if (auto terminal = cast(Terminal)(cast(SymbolNode) node).symbol)
                    parserTerminals[terminal] = true;
    }

    foreach (terminal; eag.plainHyperGrammar.terminals)
    {
        if (terminal !in parserTerminals)
            continue;

        terminalNames[terminal.index] = terminal.toString;
    }

    if (lexicalRoots.empty)
    {
        foreach (terminal; eag.plainHyperGrammar.terminals)
        {
            if (terminal !in parserTerminals)
                continue;

            const Position position = positions.get(terminal, UndefPos);
            auto alternative = new Alternative(new LhsNode(candidate, position),
                [new SymbolNode(terminalHelper(terminal), position)], position);

            builder.add(alternative);
            candidates[alternative] = LexerCandidate(LexerCandidate.Kind.terminal,
                terminal.index);
        }
    }

    foreach (rule; eag.plainHyperGrammar.rules)
    {
        Nonterminal sourceNonterminal = rule.lhs.nonterminal;

        if (!properties.isLexicalNonterminal(sourceNonterminal))
            continue;

        foreach (alternativeIndex, alternative; rule.alternatives)
        {
            Node[] rhs = null;
            foreach (node; alternative.rhs)
            {
                auto symbolNode = cast(SymbolNode) node;

                assert(symbolNode !is null);

                if (auto terminal = cast(Terminal) symbolNode.symbol)
                    rhs ~= new SymbolNode(terminalHelper(terminal), symbolNode.position);
                else
                {
                    auto nonterminal = cast(Nonterminal) symbolNode.symbol;

                    assert(nonterminal in lexicalNonterminals);
                    rhs ~= new SymbolNode(lexicalNonterminals[nonterminal], symbolNode.position);
                }
            }

            auto copiedAlternative = new Alternative(
                new LhsNode(lexicalNonterminals[sourceNonterminal], alternative.lhs.position),
                rhs, alternative.position);

            builder.add(copiedAlternative);
            rules[copiedAlternative] = LexerRule(sourceNonterminal.index, alternativeIndex + 1, size_t.max);
        }
    }

    foreach (nonterminal, isLexicalRoot; lexicalRoots)
    {
        if (!isLexicalRoot)
            continue;

        const Position position = eag.plainHyperGrammar.ruleOf(nonterminal).lhs.position;
        auto alternative = new Alternative(new LhsNode(candidate, position),
            [new SymbolNode(lexicalNonterminals[nonterminal], position)], position);

        builder.add(alternative);
        candidates[alternative] = LexerCandidate(LexerCandidate.Kind.nonterminal, nonterminal.index);
    }

    return LexerGrammar(builder.getGrammar(root), tokenEnd, helpersByTerminal, candidates, rules,
        lexicalNonterminalOwners, terminalNames, nonterminalNames);
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

module gamma.input.earley.AffixForm;

import gamma.grammar.affixes.Variable;
import gamma.grammar.SymbolNode;

/**
 * This immutable value object represents a possible affix form.
 * The sentential form is represented as a sequence of symbol nodes
 * of terminals and nonterminals of a grammar.
 * In addition, for each nonterminal occurrence,
 * the corresponding affix variable is specified.
 */
public class AffixForm
{
    private SymbolNode[] symbolNodes_;

    private Variable[] variables_;

    public this(SymbolNode[] symbolNodes, Variable[] variables)
    {
        this.symbolNodes_ = symbolNodes.dup;
        this.variables_ = variables.dup;
    }

    public bool isSingleVariable() const
    {
        return symbolNodes_.length == 1 && variables_.length == 1;
    }

    public SymbolNode[] symbolNodes()
    {
        return this.symbolNodes_;
    }

    public Variable[] variables()
    {
        return this.variables_;
    }
}

version (unittest):

import gamma.grammar.Grammar;
import gamma.grammar.Symbol;
import std.range;
import std.string : lineSplitter;

/**
 * Builds an AffixForm from a whitespace-separated sequence of symbols.
 * Uppercase symbols are looked up as nonterminals; lowercase symbols as terminals.
 */
AffixForm affixForm(Grammar grammar, const string line)
in (line.lineSplitter.drop(1).empty)
{
    import gamma.grammar.Nonterminal : Nonterminal;
    import gamma.util.Position : Position;
    import std.algorithm : chunkBy, filter, find, map;
    import std.conv : to;
    import std.typecons : Nullable, tuple;
    import std.uni : isNumber, isWhite;

    SymbolNode[] symbolNodes;
    Variable[] variables;

    auto tokens = line.enumerate(1)
        .chunkBy!((a, b) => a.value.isWhite == b.value.isWhite)
        .filter!(chunk => !chunk.front.value.isWhite)
        .map!(chunk => tuple(chunk.front.index, chunk.map!(p => p.value).to!string));

    foreach (col, token; tokens)
    {
        const position = Position("string", 1, col, line);
        const unequal = token.front == '!';

        if (unequal)
            token.popFront;

        auto digits = token.find!isNumber;
        Symbol symbol = grammar.symbolFromGrammar(token.dropBack(digits.length));
        Nullable!string number;

        if (!digits.empty)
            number = digits.idup;

        symbolNodes ~= new SymbolNode(symbol, position);
        if (auto nonterminal = cast(Nonterminal) symbol)
            variables ~= new Variable(unequal, nonterminal, number, position);
    }

    return new AffixForm(symbolNodes, variables);
}

private Symbol symbolFromGrammar(Grammar grammar, const string representation)
{
    import std.algorithm : find;
    import std.format : format;
    import std.uni : isUpper;

    if (representation.front.isUpper)
    {
        auto found = grammar.nonterminals.find!(symbol => symbol.toString == representation);

        assert(!found.empty, format!"unknown nonterminal: %s"(representation));

        return found.front;
    }
    else
    {
        auto found = grammar.terminals.find!(symbol => symbol.toString == representation);

        assert(!found.empty, format!"unknown terminal: %s"(representation));

        return found.front;
    }
}

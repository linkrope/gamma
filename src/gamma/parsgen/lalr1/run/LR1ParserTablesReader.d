module gamma.parsgen.lalr1.run.LR1ParserTablesReader;

import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.GrammarBuilder;
import gamma.grammar.Node;
import gamma.grammar.Nonterminal;
import gamma.grammar.Rule;
import gamma.grammar.Symbol;
import gamma.grammar.SymbolNode;
import gamma.grammar.Terminal;
import gamma.parsgen.lalr1.OrderedLR1Tables;
import gamma.util.Position;
import std.algorithm;
import std.exception;
import std.format;
import std.json;
import std.stdio;

/**
 * Reads an OrderedLR1Tables representation from a given input file.
 */
public class LR1ParserTablesReader
{
    private OrderedLR1Tables.Action[][] parserActionRows;

    private OrderedLR1Tables.Goto[][] gotoRows;

    private GrammarBuilder grammarBuilder;

    private Nonterminal[size_t] index2Nonterminal;

    private Terminal[size_t] index2Terminal;

    private Alternative[size_t] index2Alternative;

    private long maxState;

    public struct SimplePosition
    {
        alias position this;

        public Position position;

        private string repr;

        public this(string repr)
        {
            this.repr = repr;
        }

        public void markError(string message)
        {
            import log;

            error!"%s: %s"(repr, message);
        }
    }

    static private string ruleReprFor(Alternative alt)
    {
        return format!"%s ::=%-( %s%)"(alt.lhs.symbol, alt.rhs.map!(node => (cast(SymbolNode) node).symbol));
    }

    private this()
    {
        this.maxState = -1;
    }

    public static OrderedLR1Tables read(File input)
    {
        import std.array : array;

        auto text = cast(char[]) input.byChunk(4096).joiner.array;
        auto value = parseJSON(text);

        return new LR1ParserTablesReader().parseLR1Parser(value);
    }

    private OrderedLR1Tables parseLR1Parser(JSONValue value)
    {
        import gamma.parsgen.lalr1.run.OrderedLR1TablesImpl : OrderedLR1TablesImpl;

        JSONValue[string] object = value.object;
        Grammar grammar = parseGrammar(object["grammar"]);

        parseActions(object["states"]);
        return new OrderedLR1TablesImpl(grammar, this.parserActionRows, this.gotoRows);
    }

    private Grammar parseGrammar(JSONValue value)
    {
        JSONValue[string] object = value.object;

        parseNonterminals(object["nonterminals"]);
        parseTerminals(object["terminals"]);
        parseRules(object["rules"]);

        Nonterminal startSymbol = parseStartSymbol(object["startSymbol"]);

        Grammar grammar = grammarBuilder.getGrammar(startSymbol);

        enforce(startSymbol == grammar.startSymbol,
            "sorry, not able to build a grammar with the required start symbol");

        checkGrammar(grammar);
        return grammar;
    }

    private void parseNonterminals(JSONValue value)
    {
        foreach (nonterminalValue; value.array)
        {
            JSONValue[string] object = nonterminalValue.object;
            const index = object["index"].integer;
            const repr = object["repr"].str;
            Nonterminal nonterminal = grammarBuilder.buildNonterminal(repr);

            enforce(nonterminal.index == index,
                "bad nonterminal index...");


            index2Nonterminal[index] = nonterminal;
        }
    }

    private void parseTerminals(JSONValue value)
    {
        foreach (terminalValue; value.array)
        {
            JSONValue[string] object = terminalValue.object;
            const index = object["index"].integer;
            const repr = object["repr"].str;
            Terminal terminal = grammarBuilder.buildTerminal(repr);

            enforce(terminal.index == index,
                "bad terminal index...");


            index2Terminal[index] = terminal;
        }
    }

    private void parseRules(JSONValue value)
    {
        foreach (ruleValue; value.array)
            parseRule(ruleValue);
    }

    private void parseRule(JSONValue value)
    {
        JSONValue[string] object = value.object;
        const index = object["lhs"].integer;
        Nonterminal lhs = index2Nonterminal[index];

        foreach (alternativeValue; object["alternatives"].array)
            parseAlternative(lhs, alternativeValue);
    }

    private void parseAlternative(Nonterminal lhs, JSONValue value)
    {
        JSONValue[string] object = value.object;
        const index = object["index"].integer;

        Node[] rhs;

        foreach (nodeValue; object["rhs"].array)
        {
            Symbol symbol;

            if (nodeValue.object["type"].str == "nonterminal")
                symbol = parseNonterminal(nodeValue);
            else if (nodeValue.object["type"].str == "terminal")
                symbol = parseTerminal(nodeValue);
            else
                break;
            rhs ~= new SymbolNode(symbol, SimplePosition(symbol.toString));
        }

        auto alternative = new Alternative(
            new SymbolNode(lhs, SimplePosition(lhs.toString)),
            rhs,
            SimplePosition(format!"alternative #%s"(index)));

        this.index2Alternative[index] = alternative;
        grammarBuilder.add(alternative);
    }

    private Nonterminal parseNonterminal(JSONValue value)
    {
        JSONValue[string] object = value.object;
        const index = object["index"].integer;
        Nonterminal nonterminal = index2Nonterminal[index];

        return nonterminal;
    }

    private Terminal parseTerminal(JSONValue value)
    {
        JSONValue[string] object = value.object;
        const index = object["index"].integer;
        Terminal terminal = index2Terminal[index];

        return terminal;
    }

    private Nonterminal parseStartSymbol(JSONValue value)
    {
        JSONValue[string] object = value.object;
        const index = object["index"].integer;
        Nonterminal nonterminal = index2Nonterminal[index];

        return nonterminal;
    }

    private void parseActions(JSONValue value)
    {
        foreach (stateValue; value.array)
        {
            JSONValue[string] object = stateValue.object;
            const index = object["index"].integer;

            enforce(index == parserActionRows.length,
                format!"illegal state %s"(index));

            OrderedLR1Tables.Action[] parserActionRow;

            foreach (actionValue; object["actions"].array)
                if (actionValue.object["type"].str == "shift")
                    parserActionRow ~= parseShift(actionValue);
                else if (actionValue.object["type"].str == "reduce")
                    parserActionRow ~= parseReduce(actionValue);
                else if (actionValue.object["type"].str == "halt")
                    parserActionRow ~= parseHalt(actionValue);
            parserActionRows ~= parserActionRow;

            OrderedLR1Tables.Goto[] gotoRow;

            foreach (transitionValue; object["transitions"].array)
                gotoRow ~= parseGoto(transitionValue);
            gotoRows ~= gotoRow;
        }

        enforce(this.maxState < parserActionRows.length,
            "something went wrong...");
    }

    private OrderedLR1Tables.Shift parseShift(JSONValue value)
    {
        Terminal lookahead = parseOnTerminal(value);
        const toState = parseTo(value);
        const continues = parseContinues(value);
        OrderedLR1Tables.Shift shift = new OrderedLR1Tables.Shift(lookahead, toState);

        shift.isContinuationAction = continues;
        return shift;
    }

    private OrderedLR1Tables.Reduce parseReduce(JSONValue value)
    {
        Terminal lookahead = parseOnTerminal(value);
        Alternative alternative = parseRuleAlt(value);
        const continues = parseContinues(value);
        OrderedLR1Tables.Reduce reduce = new OrderedLR1Tables.Reduce(lookahead, alternative);

        reduce.isContinuationAction = continues;
        return reduce;
    }

    private OrderedLR1Tables.Halt parseHalt(JSONValue value)
    {
        Terminal lookahead = parseOnTerminal(value);
        const continues = parseContinues(value);
        OrderedLR1Tables.Halt halt = new OrderedLR1Tables.Halt(lookahead);

        halt.isContinuationAction = continues;
        return halt;
    }

    private OrderedLR1Tables.Goto parseGoto(JSONValue value)
    {
        Nonterminal lhs = parseOnNonterminal(value);
        const to = parseTo(value);
        OrderedLR1Tables.Goto goTo = new OrderedLR1Tables.Goto(lhs, to);

        return goTo;
    }

    private Terminal parseOnTerminal(JSONValue value)
    {
        JSONValue[string] object = value.object;
        const on = object["on"].integer;
        Terminal terminal = index2Terminal[on];

        return terminal;
    }

    private Nonterminal parseOnNonterminal(JSONValue value)
    {
        JSONValue[string] object = value.object;
        const on = object["on"].integer;
        Nonterminal lhs = index2Nonterminal[on];

        return lhs;
    }

    private long parseTo(JSONValue value)
    {
        JSONValue[string] object = value.object;
        const to = object["to"].integer;

        maxState = max(maxState, to); // for final check if all referred stated have been seen

        return to;
    }

    private Alternative parseRuleAlt(JSONValue value)
    {
        JSONValue[string] object = value.object;
        const ruleAlt = object["ruleAlt"].integer;
        Alternative alternative = index2Alternative[ruleAlt];

        return alternative;
    }

    private bool parseContinues(JSONValue value)
    {
        JSONValue[string] object = value.object;

        if ("continues" in object)
            return object["continues"].boolean;
        return false;
    }

    /**
     * Checks whether this.grammar is acceptable for the parser generator.
     * <p>
     * The following checks are performed:<br>
     * (1) that this.grammar is a pure context-free grammar and <br>
     * (2) that this.grammar is an "extended" context-free grammar,
     * i.e. its start symbol &lt;ExtendedStartSymbol> has only one alternative
     * &lt;ExtendedStartSymbol> ::= &lt;StartSymbol> &lt;eofSymbol> such that
     * &lt;StartSymbol> and &lt;ExtendedStartSymbol> are Nonterminals, &lt;eofSymbol> is a Terminal,
     * and both &lt;ExtendedStartSymbol> and &lt;eofSymbol> occur only in this grammar rule.
     * <p>
     * If this.grammar is not acceptable, the method throws an IllegalArgumentException.
     */
    private void checkGrammar(Grammar grammar)
    {
        Rule startRule = grammar.ruleOf(grammar.startSymbol);

        enforce(startRule.alternatives.length == 1,
            "not an extended grammar");

        auto startAlternative = cast(Alternative) startRule.alternatives[0];

        enforce(startAlternative.rhs.length == 2,
            "not an extended grammar");
        enforce(cast(Nonterminal)((cast(SymbolNode) startAlternative.rhs[0]).symbol),
            "not an extended grammar");

        Symbol extendedStartSymbol = grammar.startSymbol;
        Symbol eofSymbol = (cast(SymbolNode) startAlternative.rhs[1]).symbol;

        enforce(cast(Terminal) eofSymbol,
            "not an extended grammar");

        foreach (oldRule; grammar.rules)
        {
            foreach (alternative; oldRule.alternatives)
            {
                if (alternative == startAlternative)
                    continue;

                foreach (node; alternative.rhs)
                {
                    enforce(cast(SymbolNode) node,
                        "not a pure context-free grammar");

                    auto symbolNode = cast(SymbolNode) node;

                    enforce(symbolNode.symbol != extendedStartSymbol && symbolNode.symbol != eofSymbol,
                        "not an extended grammar");
                }
            }
        }
    }
}

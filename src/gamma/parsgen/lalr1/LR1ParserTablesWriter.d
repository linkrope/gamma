module gamma.parsgen.lalr1.LR1ParserTablesWriter;

import gamma.grammar.Alternative;
import gamma.grammar.Node;
import gamma.grammar.Nonterminal;
import gamma.grammar.Rule;
import gamma.grammar.Symbol;
import gamma.grammar.SymbolNode;
import gamma.grammar.Terminal;
import gamma.parsgen.lalr1.OrderedLR1Tables;
import std.algorithm;
import std.array;
import std.json;
import std.stdio;

/**
 * Writes an OrderedLR1Tables representation to a given output file.
 */
public static void write(OrderedLR1Tables parserTables, File output)
{
    JSONValue[string] grammarObject;
    JSONValue[] nonterminals;

    foreach (nonterminal; parserTables.grammar.nonterminals)
        nonterminals ~= JSONValue([
            "index": JSONValue(nonterminal.index),
            "repr": JSONValue(nonterminal.toString),
        ]);
    grammarObject["nonterminals"] = nonterminals;

    JSONValue[] terminals;

    foreach (terminal; parserTables.grammar.terminals)
        terminals ~= JSONValue([
            "index": JSONValue(terminal.index),
            "repr": JSONValue(terminal.toString),
        ]);
    grammarObject["terminals"] = terminals;

    JSONValue[] rules;
    size_t altIndex = 0;
    size_t[Alternative] alt2IndexMap;

    foreach (rule; parserTables.grammar.rules)
    {
        JSONValue[string] ruleObject;

        if (rule.alternatives.length == 0)
            continue;

        ruleObject["lhs"] = (cast(Nonterminal)(cast(Alternative) rule.alternatives[0]).lhs.symbol).index;

        JSONValue[] alternatives;

        foreach (alternative; rule.alternatives)
        {
            JSONValue[string] alternativeObject;

            alternativeObject["index"] = altIndex;
            alt2IndexMap[alternative] = altIndex;
            ++altIndex;

            JSONValue[] symbols;

            foreach (node; alternative.rhs)
            {
                assert(cast(SymbolNode) node);

                auto symbol = (cast(SymbolNode) node).symbol;

                if (cast(Terminal) symbol)
                    symbols ~= JSONValue([
                        "type": JSONValue("terminal"),
                        "index": JSONValue((cast(Terminal) symbol).index),
                    ]);
                else if (cast(Nonterminal) symbol)
                    symbols ~= JSONValue([
                        "type": JSONValue("nonterminal"),
                        "index": JSONValue((cast(Nonterminal) symbol).index)
                    ]);
            }
            alternativeObject["rhs"] = symbols;
            alternatives ~= JSONValue(alternativeObject);
        }
        ruleObject["alternatives"] = alternatives;
        rules ~= JSONValue(ruleObject);
    }
    grammarObject["rules"] = rules;
    grammarObject["startSymbol"] = ["index": parserTables.grammar.startSymbol.index];

    JSONValue[] states;

    foreach (state; 0 .. parserTables.stateCount)
    {
        JSONValue[string] stateObject;

        stateObject["index"] = state;

        JSONValue[] actions;

        foreach (action; parserTables.getSortedParserActionRow(state))
        {
            JSONValue[string] actionObject;

            actionObject["on"] = action.lookahead.index;
            if (cast(OrderedLR1Tables.Shift) action)
            {
                actionObject["type"] = "shift";
                actionObject["to"] = (cast(OrderedLR1Tables.Shift) action).state;
            }
            else if (cast(OrderedLR1Tables.Reduce) action)
            {
                OrderedLR1Tables.Reduce ra = cast(OrderedLR1Tables.Reduce) action;

                actionObject["type"] = "reduce";
                actionObject["ruleAlt"] = alt2IndexMap[ra.alternative];
            }
            else if (cast(OrderedLR1Tables.Halt) action)
            {
                actionObject["type"] = "halt";
            }
            if (action.isContinuationAction)
                actionObject["continues"] = true;
            actions ~= JSONValue(actionObject);
        }
        stateObject["actions"] = actions;

        JSONValue[] transitions;

        foreach (g; parserTables.getSortedGotoRow(state))
            transitions ~= JSONValue([
                "on": JSONValue(g.lhs.index),
                "to": JSONValue(g.state),
            ]);
        stateObject["transitions"] = transitions;
        states ~= JSONValue(stateObject);
    }

    JSONValue value = [
        "grammar": JSONValue(grammarObject),
        "states": JSONValue(states),
        ];

    output.writeln(value.toPrettyString);
}

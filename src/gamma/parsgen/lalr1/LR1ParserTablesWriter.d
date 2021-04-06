module gamma.parsgen.lalr1.LR1ParserTablesWriter;

import gamma.grammar.Alternative;
import gamma.grammar.Node;
import gamma.grammar.Nonterminal;
import gamma.grammar.Rule;
import gamma.grammar.Symbol;
import gamma.grammar.SymbolNode;
import gamma.grammar.Terminal;
import gamma.parsgen.lalr1.OrderedLR1Tables;
import std.stdio;

/**
 * Writes an OrderedLR1Tables instance to a given OutputStream.
 * This implementation uses an XML representation for output.
 *
 * @author SöKa
 */
public static void write(OrderedLR1Tables parserTables, File output)
{
    output.writeln("<?xml version='1.0' encoding='UTF-8' standalone='yes'?>");
    output.writeln("<lr1-parser>");
    output.writeln("<grammar>");
    output.writeln("<nonterminals>");
    foreach (nonterminal; parserTables.grammar.nonterminals)
        output.writefln!`<add index="%s" repr="%s"/>`(nonterminal.index, nonterminal);
    output.writeln("</nonterminals>");
    output.writeln("<terminals>");
    foreach (terminal; parserTables.grammar.terminals)
        output.writefln!`<add index="%s" repr="%s"/>`(terminal.index, terminal);
    output.writeln("</terminals>");
    output.writeln("<rules>");

    size_t altIndex = 0;
    size_t[Alternative] alt2IndexMap;

    foreach (rule; parserTables.grammar.rules)
    {
        if (rule.alternatives.length == 0)
            continue;
        output.writefln!`<rule lhs="%s">`((cast(Nonterminal)(cast(Alternative) rule.alternatives[0]).lhs.symbol).index);
        foreach (alternative; rule.alternatives)
        {
            output.writefln!`<alternative index="%s">`(altIndex);
            alt2IndexMap[alternative] = altIndex;
            ++altIndex;
            foreach (node; alternative.rhs)
            {
                assert(cast(SymbolNode) node);

                Symbol s = (cast(SymbolNode) node).symbol;

                if (cast(Terminal) s)
                    output.writefln!`<terminal index="%s"/>`((cast(Terminal) s).index);
                else if (cast(Nonterminal) s)
                    output.writefln!`<nonterminal index="%s"/>`((cast(Nonterminal) s).index);
            }
            output.writeln("</alternative>");
        }
        output.writeln("</rule>");
    }
    output.writeln("</rules>");
    output.writefln!`<startsymbol index="%s"/>`(parserTables.grammar.startSymbol.index);
    output.writeln("</grammar>");
    output.writeln("<actions>");
    foreach (state; 0 .. parserTables.stateCount)
    {
        output.writefln!`<state index="%s"`(state);
        foreach (action; parserTables.getSortedParserActionRow(state))
        {
            const la = action.lookahead.index;

            if (cast(OrderedLR1Tables.Shift) action)
            {
                output.writef!`<shift on="%s" to="%s"`(la, (cast(OrderedLR1Tables.Shift) action).state);
            }
            else if (cast(OrderedLR1Tables.Reduce) action)
            {
                OrderedLR1Tables.Reduce ra = cast(OrderedLR1Tables.Reduce) action;

                output.writef!`<reduce on="%s" rulealt="%s"`(la, alt2IndexMap[ra.alternative]);
            }
            else if (cast(OrderedLR1Tables.Halt) action)
            {
                output.writef!`<halt on="%s"`(la);
            }
            if (action.isContinuationAction)
                output.write(` continues="true"`);
            output.writeln("/>");
        }
        foreach (g; parserTables.getSortedGotoRow(state))
            output.writefln!`<goto on="%s" to="%s"/>`(g.lhs.index, g.state);
        output.writeln("</state>");
    }
    output.writeln("</actions>");
    output.writeln("</lr1-parser>");
}

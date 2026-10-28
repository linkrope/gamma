module gamma.parsgen.lalr1.LR1ParserTablesWriter;

import gamma.parsgen.lalr1.OrderedLR1Tables;
import gamma.parsgen.lalr1.ParserGrammarBuilder : ParserGrammar;

public void write(string fileName, string moduleName,
    OrderedLR1Tables parserTables, ParserGrammar parserGrammar)
{
    import gamma.grammar.Alternative : Alternative;
    import io : Input;
    import std.algorithm : map;
    import std.array : array;
    import std.exception : enforce;
    import std.format : format;
    import std.range : enumerate;
    import std.stdio : File;

    size_t[Alternative] alternativeIndices = null;
    size_t alternativeIndex = 0;

    foreach (rule; parserTables.grammar.rules)
        foreach (alternative; rule.alternatives)
            alternativeIndices[alternative] = alternativeIndex++;

    size_t[] actionOffsets = [0];
    string[] actions = null;

    foreach (state; 0 .. parserTables.stateCount)
    {
        foreach (action; parserTables.getSortedParserActionRow(state))
        {
            if (auto shift = cast(OrderedLR1Tables.Shift) action)
            {
                actions ~= format!"Action(Shift(%s, %s, %s))"(
                    action.lookahead.index, shift.state, action.isContinuationAction);
            }
            else if (auto reduce = cast(OrderedLR1Tables.Reduce) action)
            {
                actions ~= format!"Action(Reduce(%s, %s, %s))"(
                    action.lookahead.index, alternativeIndices[reduce.alternative], action.isContinuationAction);
            }
            else
            {
                actions ~= format!"Action(Halt(%s, %s))"(
                    action.lookahead.index, action.isContinuationAction);
            }
        }
        actionOffsets ~= actions.length;
    }

    const actionOffsetLiterals = actionOffsets
        .map!(offset => format!"%s"(offset))
        .array;

    size_t[] gotoOffsets = [0];
    string[] gotos = null;

    foreach (state; 0 .. parserTables.stateCount)
    {
        foreach (goTo; parserTables.getSortedGotoRow(state))
            gotos ~= format!"Goto(%s, %s)"(goTo.lhs.index, goTo.state);
        gotoOffsets ~= gotos.length;
    }

    const gotoOffsetLiterals = gotoOffsets
        .map!(offset => format!"%s"(offset))
        .array;

    string[] rules = null;
    foreach (rule; parserTables.grammar.rules)
    {
        foreach (count, alternative; rule.alternatives.enumerate)
        {
            rules ~= format!"Rule(%s, %s, %s)"(
                alternative.lhs.nonterminal.index,
                alternative.rhs.length,
                count + 1,
            );
        }
    }

    string[] terminals = null;

    foreach (parserTerminal; parserTables.grammar.terminals)
    {
        if (auto terminal = parserTerminal in parserGrammar.terminals)
            terminals ~= format!"Symbol(%s, %s)"((*terminal).index, (*terminal).toString.quoted);
        else
            terminals ~= format!"Symbol(size_t.max, %s)"(parserTerminal.toString.quoted);
    }

    string[] nonterminals = null;

    foreach (parserNonterminal; parserTables.grammar.nonterminals)
    {
        if (auto nonterminal = parserNonterminal in parserGrammar.nonterminals)
            nonterminals ~= format!"Symbol(%s, %s)"((*nonterminal).index, (*nonterminal).toString.quoted);
        else
            nonterminals ~= format!"Symbol(size_t.max, %s)"(parserNonterminal.toString.quoted);
    }

    enum fixName = "lrtables.fix.d";
    Input fix = Input(fixName, import(fixName));
    File output = File(fileName, "w");

    void includeFix(char terminator)
    {
        while (fix.front != terminator)
        {
            enforce(fix.front != 0, "unexpected end of lrtables.fix.d");
            output.write(fix.front);
            fix.popFront;
        }
        fix.popFront;
    }

    includeFix('$');
    output.write(moduleName);
    includeFix('$');
    output.write(parserTables.eof.index);
    includeFix('$');
    output.write(actions.arrayLiteral);
    includeFix('$');
    output.write(actionOffsetLiterals.arrayLiteral);
    includeFix('$');
    output.write(gotos.arrayLiteral);
    includeFix('$');
    output.write(gotoOffsetLiterals.arrayLiteral);
    includeFix('$');
    output.write(rules.arrayLiteral);
    includeFix('$');
    output.write(terminals.arrayLiteral);
    includeFix('$');
    output.write(nonterminals.arrayLiteral);
    includeFix('$');
    output.close;
}

private string arrayLiteral(const string[] items)
{
    import std.array : join;
    import std.range : empty;

    enum indent = "    ";

    if (items.empty)
        return "[]";

    return "[\n" ~ indent ~ indent ~ items.join(",\n" ~ indent ~ indent) ~ "\n" ~ indent ~ "]";
}

private string quoted(const string text)
{
    import std.string : translate;

    return `"` ~ text.translate(['\\': `\\`, '"': `\"`]) ~ `"`;
}

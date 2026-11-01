module gamma.parsgen.lalr1.LR1TablesWriter;

import gamma.grammar.Alternative;
import gamma.grammar.Nonterminal;
import gamma.grammar.Terminal;
import gamma.parsgen.lalr1.FixWriter : includeFix;
import gamma.parsgen.lalr1.OrderedLR1Tables;
import std.stdio : File;

public struct LR1Tables
{
    private string eofTerminal;

    private string actions;

    private string actionOffsets;

    private string gotos;

    private string gotoOffsets;

    private string rules;

    private string terminals;

    private string nonterminals;

    private string candidateTerminals;

    private string terminalNames;

    private size_t[Alternative] alternativeIndices;

    public size_t alternativeIndex(Alternative alternative) const
    in (alternative in alternativeIndices)
    {
        return alternativeIndices[alternative];
    }

    public void setLexerMetadata(const size_t[] candidateTerminals,
        const string[] terminalNames)
    {
        string[] names;
        foreach (terminalName; terminalNames)
            names ~= terminalName.quoted;

        this.candidateTerminals = candidateTerminals.literal;
        this.terminalNames = names.arrayLiteral;
    }

}

public LR1Tables createTables(OrderedLR1Tables parserTables,
    Terminal[Terminal] parserTerminals = null,
    Nonterminal[Nonterminal] parserNonterminals = null)
{
    import std.format : format;
    import std.range : enumerate;

    LR1Tables result;
    size_t alternativeIndex = 0;

    foreach (rule; parserTables.grammar.rules)
        foreach (alternative; rule.alternatives)
            result.alternativeIndices[alternative] = alternativeIndex++;

    size_t[] actionOffsets = [0];
    string[] actions = null;

    foreach (state; 0 .. parserTables.stateCount)
    {
        foreach (action; parserTables.getSortedParserActionRow(state))
        {
            if (auto shift = cast(OrderedLR1Tables.Shift) action)
                actions ~= format!"Action(Shift(%s, %s, %s))"(
                    action.lookahead.index, shift.state, action.isContinuationAction);
            else if (auto reduce = cast(OrderedLR1Tables.Reduce) action)
                actions ~= format!"Action(Reduce(%s, %s, %s))"(
                    action.lookahead.index, result.alternativeIndex(reduce.alternative),
                    action.isContinuationAction);
            else
                actions ~= format!"Action(Halt(%s, %s))"(
                    action.lookahead.index, action.isContinuationAction);
        }
        actionOffsets ~= actions.length;
    }

    size_t[] gotoOffsets = [0];
    string[] gotos = null;

    foreach (state; 0 .. parserTables.stateCount)
    {
        foreach (goTo; parserTables.getSortedGotoRow(state))
            gotos ~= format!"Goto(%s, %s)"(goTo.lhs.index, goTo.state);
        gotoOffsets ~= gotos.length;
    }

    string[] rules = null;

    foreach (rule; parserTables.grammar.rules)
    {
        foreach (count, alternative; rule.alternatives.enumerate)
            rules ~= format!"Rule(%s, %s, %s)"(
                alternative.lhs.nonterminal.index, alternative.rhs.length, count + 1);
    }

    string[] terminals = null;

    foreach (parserTerminal; parserTables.grammar.terminals)
        terminals ~= symbolLiteral(parserTerminal, parserTerminals);

    string[] nonterminals = null;

    foreach (parserNonterminal; parserTables.grammar.nonterminals)
        nonterminals ~= symbolLiteral(parserNonterminal, parserNonterminals);

    result.eofTerminal = format!"%s"(parserTables.eof.index);
    result.actions = actions.arrayLiteral;
    result.actionOffsets = actionOffsets.literal;
    result.gotos = gotos.arrayLiteral;
    result.gotoOffsets = gotoOffsets.literal;
    result.rules = rules.arrayLiteral;
    result.terminals = terminals.arrayLiteral;
    result.nonterminals = nonterminals.arrayLiteral;
    result.candidateTerminals = "[]";
    result.terminalNames = "[]";
    return result;
}

public void writeModule(string fileName, string moduleName, LR1Tables tables)
{
    import io : Input;
    enum fixName = "lrtables.fix.d";
    Input fix = Input(fixName, import(fixName));
    File output = File(fileName, "w");

    includeFix(fix, output, '$', fixName);
    output.write(moduleName);
    includeFix(fix, output, '$', fixName);
    output.write(tables.eofTerminal);
    includeFix(fix, output, '$', fixName);
    output.write(tables.actions);
    includeFix(fix, output, '$', fixName);
    output.write(tables.actionOffsets);
    includeFix(fix, output, '$', fixName);
    output.write(tables.gotos);
    includeFix(fix, output, '$', fixName);
    output.write(tables.gotoOffsets);
    includeFix(fix, output, '$', fixName);
    output.write(tables.rules);
    includeFix(fix, output, '$', fixName);
    output.write(tables.terminals);
    includeFix(fix, output, '$', fixName);
    output.write(tables.nonterminals);
    includeFix(fix, output, '$', fixName);
    output.write(tables.candidateTerminals);
    includeFix(fix, output, '$', fixName);
    output.write(tables.terminalNames);
    includeFix(fix, output, '$', fixName);
    output.close;
}

public string quoted(const string text)
{
    import std.string : translate;

    return `"` ~ text.translate(['\\': `\\`, '"': `\"`]) ~ `"`;
}

private string symbolLiteral(ParserSymbol, Symbol)(ParserSymbol parserSymbol,
    Symbol[ParserSymbol] parserSymbols)
{
    import std.format : format;

    if (auto symbol = parserSymbol in parserSymbols)
        return format!"Symbol(%s, %s)"((*symbol).index, (*symbol).toString.quoted);

    return format!"Symbol(size_t.max, %s)"(parserSymbol.toString.quoted);
}

private string arrayLiteral(const string[] items)
{
    import std.array : join;
    import std.range : empty;

    return items.empty ? "[]" : "[\n        " ~ items.join(",\n        ") ~ "\n    ]";
}

private string literal(const size_t[] values)
{
    import std.format : format;

    return format!"[%(%s, %)]"(values);
}

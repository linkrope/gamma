module gamma.parsgen.lalr1.ParserSymbol;

interface ParserSymbol
{
    int nr();

    string toString();

    bool isTerminal();

    bool isNonterminal();
}

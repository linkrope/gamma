module gamma.parsgen.lalr1.ParserGenerator;

import gamma.grammar.Grammar;

public interface ParserGenerator
{
    void[] computeParser(Grammar grammar);

    void emit(/* ... */);
}

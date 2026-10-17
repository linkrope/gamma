module gamma.input.EAGBuilder_test;

import gamma.input.EAGBuilder : toEAG;
import gamma.input.epsilang.analyzer : EAG;
import gamma.input.epsilang.parser : Parser;
import io : Input;
import std.string : outdent, strip;

@("build a direct operator's signature")
unittest
{
    const source = `
        n = | '1' n.

        S: ( <+ '1': n> '1' ).
        `.outdent.strip;
    auto parser = new Parser(Input("test.eag", source));

    parser.parseSpecification;

    assert(parser.getErrorCount == 0);

    auto hyperGrammar = parser.buildHyperGrammar;

    assert(hyperGrammar !is null);

    auto eag = EAG(parser.buildMetaGrammar, hyperGrammar, hyperGrammar.plainHyperGrammar,
        parser.getLexicalMetaNonterminals, parser.getLexicalHyperNonterminals).toEAG;
    auto sig = eag.HNont[eag.StartSym].Sig;

    assert(eag.DomBuf[sig] > 0);
    assert(eag.DomBuf[sig + 1] == 0);
}

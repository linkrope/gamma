module gamma.input.epsilang.parser_test;

import gamma.grammar.Grammar;
import gamma.grammar.GrammarProperties;
import gamma.grammar.hyper.EBNFConverter : convert;
import gamma.input.epsilang.parser : Parser;
import io : Input;
import std.format : format;

// These tests deliberately exercise the complete Gamma input pipeline.
// The EBNF operator rules are owned by the parser, so constructing a Grammar
// by hand would not cover the anonymous-nonterminal bookkeeping performed
// while parsing a real .eag file.

@("parse a direct EBNF group wrapper into a complete plain grammar")
unittest
{
    const source = `
        n = | '1' n.

        S:
            ( <+ '1': n> '1'
            ).
        `;

    parseAndConvertHyperGrammar(source).assertCompletePlainGrammar;
}

@("parse a nested EBNF group into a complete plain grammar")
unittest
{
    const source = `
        n = | '1' n.

        S:
            'a'
            ( <+ '1': n> '1'
            )
            'a'.
        `;

    parseAndConvertHyperGrammar(source).assertCompletePlainGrammar;
}

@("parse a direct EBNF option wrapper into a complete plain grammar")
unittest
{
    const source = `
        n = | '1' n.

        S:
            [ <+ '1': n> '1'
            ] <+ : n>.
        `;

    parseAndConvertHyperGrammar(source).assertCompletePlainGrammar;
}

@("parse a nested EBNF option into a complete plain grammar")
unittest
{
    const source = `
        n = | '1' n.

        S:
            'a'
            [ <+ '1': n> '1'
            ] <+ : n>
            'a'.
        `;

    parseAndConvertHyperGrammar(source).assertCompletePlainGrammar;
}

@("parse a direct EBNF repetition wrapper into a complete plain grammar")
unittest
{
    const source = `
        n = | '1' n.

        S:
            { <+ '1' n: n> '1' <n>
            } <+ : n>.
        `;

    parseAndConvertHyperGrammar(source).assertCompletePlainGrammar;
}

@("parse a nested EBNF repetition into a complete plain grammar")
unittest
{
    const source = `
        n = | '1' n.

        S:
            'a'
            { <+ '1' n: n> '1' <n>
            } <+ : n>
            'a'.
        `;

    parseAndConvertHyperGrammar(source).assertCompletePlainGrammar;
}

private Grammar parseAndConvertHyperGrammar(string source)
{
    auto parser = new Parser(Input("parser-unittest.eag", source));

    parser.parseSpecification;
    assert(parser.getErrorCount == 0);

    auto hyperGrammar = parser.buildHyperGrammar;

    assert(hyperGrammar !is null);
    return convert(hyperGrammar);
}

private void assertCompletePlainGrammar(Grammar grammar)
{
    assert(grammar.isPlain);
    foreach (nonterminal; grammar.nonterminals)
        assert(grammar.ruleOf(nonterminal) !is null,
            format!"nonterminal %s has no rule"(nonterminal));

    // This forces the index-based property computation as well as checking
    // the structural invariant above.
    assert((new GrammarProperties(grammar)).isProductive(grammar.startSymbol));
}

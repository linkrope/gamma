module gamma.grammar.hyper.EBNFConverter_test;

import gamma.grammar.hyper.PrintingHyperVisitor : toPrettyString;
import gamma.input.epsilang.fixture : fixture;
import std.string : outdent, strip;

@("convert a direct EBNF group")
unittest
{
    const source = `
        n = | '1' n.

        S:
            ( <+ '1': n> '1'
            ).
        `.outdent.strip;
    const expected = `
        S <+ '1' : n>:
            '1'.
        `.outdent.strip;

    with (fixture)
    {
        parse(source).pass;

        assert(hyperGrammar.plainHyperGrammar.toPrettyString.strip == expected);
    }
}

@("convert a nested EBNF group")
unittest
{
    const source = `
        n = | '1' n.

        S <+ n>:
            <n> ( <+ '1': n> '1'
                )
            'a'.
        `.outdent.strip;
    const expected = `
        S <+ n: n>:
            _1 <n>
            'a'.

        _1 <+ '1' : n>:
            '1'.
        `.outdent.strip;

    with (fixture)
    {
        parse(source).pass;

        assert(hyperGrammar.plainHyperGrammar.toPrettyString.strip == expected);
    }
}

@("convert a direct EBNF option")
unittest
{
    const source = `
        n = | '1' n.

        S:
            [ <+ '1': n> '1'
            ] <+ : n>.
        `.outdent.strip;
    const expected = `
        S <+ '1' : n>:
            '1'.
        S <+ : n>: .
        `.outdent.strip;

    with (fixture)
    {
        parse(source).pass;

        assert(hyperGrammar.plainHyperGrammar.toPrettyString.strip == expected);
    }
}

@("convert a nested EBNF option")
unittest
{
    const source = `
        n = | '1' n.

        S <+ n>:
            <n> [ <+ '1': n> '1'
                ] <+ : n>
            'a'.
        `.outdent.strip;
    const expected = `
        S <+ n: n>:
            _1 <n>
            'a'.

        _1 <+ '1' : n>:
            '1'.
        _1 <+ : n>: .
        `.outdent.strip;

    with (fixture)
    {
        parse(source).pass;

        assert(hyperGrammar.plainHyperGrammar.toPrettyString.strip == expected);
    }
}

@("convert a direct EBNF repetition")
unittest
{
    const source = `
        n = | '1' n.

        S:
            { <+ '1' n: n> '1' <n>
            } <+ : n>.
        `.outdent.strip;
    const expected = `
        S <+ '1' n: n>:
            '1'
            S <n>.
        S <+ : n>: .
        `.outdent.strip;

    with (fixture)
    {
        parse(source).pass;

        assert(hyperGrammar.plainHyperGrammar.toPrettyString.strip == expected);
    }
}

@("convert a nested EBNF repetition")
unittest
{
    const source = `
        n = | '1' n.

        S <+ n>:
            <n> { <+ '1' n: n> '1' <n>
                } <+ : n>
            'a'.
        `.outdent.strip;
    const expected = `
        S <+ n: n>:
            _1 <n>
            'a'.

        _1 <+ '1' n: n>:
            '1'
            _1 <n>.
        _1 <+ : n>: .
        `.outdent.strip;

    with (fixture)
    {
        parse(source).pass;

        assert(hyperGrammar.plainHyperGrammar.toPrettyString.strip == expected);
    }
}

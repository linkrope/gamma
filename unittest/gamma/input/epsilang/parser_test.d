module gamma.input.epsilang.parser_test;

import gamma.input.epsilang.fixture : fixture;
import std.string : outdent, strip;

@("report invalid empty affix form")
unittest
{
    const source = `
        M = 'a'.

        S <+ : M>: A <>.
        A <- M>: .
        `.outdent.strip;
    const formalParamsError = `
        unexpected end of affix form for M
        test.eag:3:6 S <+ : M>: A <>.
                          ^
        `.outdent.strip;
    const actualParamsError = `
        unexpected end of affix form for M
        test.eag:3:15 S <+ : M>: A <>.
                                    ^
        `.outdent.strip;

    with (fixture())
    {
        parse(source).fail;

        assert(diagnostics == [formalParamsError, actualParamsError]);
    }
}

@("reject inconsistent formal signatures")
unittest
{
    const source = `
        n = | '1' n.

        S <+ n>:
            'a'.
        S <- n>:
            'b'.
        `.outdent.strip;
    const error = `
        formal params for S differ
        test.eag:3:3 S <+ n>:
                       ^
        test.eag:5:3 S <- n>:
                       ^
        `.outdent.strip;

    with (fixture())
    {
        parse(source).fail;

        assert(diagnostics == [error]);
    }
}

@("reject a missing formal signature on a later rule")
unittest
{
    const source = `
        n = | '1' n.

        S <+ n>: 'a'.
        S: 'b'.
        `.outdent.strip;
    const error = `
        formal params for S differ
        test.eag:3:3 S <+ n>: 'a'.
                       ^
        test.eag:4:1 S: 'b'.
                     ^
        `.outdent.strip;

    with (fixture())
    {
        parse(source).fail;

        assert(diagnostics == [error]);
    }
}

@("reject a missing formal signature on an earlier rule")
unittest
{
    const source = `
        n = | '1' n.

        S: 'a'.
        S <+ n>: 'b'.
        `.outdent.strip;
    const error = `
        formal params for S differ
        test.eag:3:1 S: 'a'.
                     ^
        test.eag:4:3 S <+ n>: 'b'.
                       ^
        `.outdent.strip;

    with (fixture())
    {
        parse(source).fail;

        assert(diagnostics == [error]);
    }
}

@("reject missing actual parameters for a nonterminal")
unittest
{
    const source = `
        n = | '1' n.

        S: A.
        A <+ '1': n>: 'a'.
        `.outdent.strip;
    const error = `
        missing actual parameters for A
        test.eag:3:4 S: A.
                        ^
        `.outdent.strip;

    with (fixture)
    {
        parse(source).fail;

        assert(diagnostics == [error]);
    }
}

@("reject missing actual parameters for a nested group")
unittest
{
    const source = `
        n = | '1' n.

        S: 'a'
            ( <+ '1': n> '1' ).
        `.outdent.strip;
    const error = `
        missing actual parameters for EBNF expression
        test.eag:4:5     ( <+ '1': n> '1' ).
                         ^
        `.outdent.strip;

    with (fixture)
    {
        parse(source).fail;

        assert(diagnostics == [error]);
    }
}

@("reject missing actual parameters for a nested option")
unittest
{
    const source = `
        n = | '1' n.

        S: 'a'
            [ <+ '1': n> '1' ] <+ : n>.
        `.outdent.strip;
    const error = `
        missing actual parameters for EBNF expression
        test.eag:4:5     [ <+ '1': n> '1' ] <+ : n>.
                         ^
        `.outdent.strip;

    with (fixture)
    {
        parse(source).fail;

        assert(diagnostics == [error]);
    }
}

@("reject missing actual parameters for a nested repetition")
unittest
{
    const source = `
        n = | '1' n.

        S: 'a'
            { <+ '1' n: n> '1' <n> } <+ : n>.
        `.outdent.strip;
    const error = `
        missing actual parameters for EBNF expression
        test.eag:4:5     { <+ '1' n: n> '1' <n> } <+ : n>.
                         ^
        `.outdent.strip;

    with (fixture)
    {
        parse(source).fail;

        assert(diagnostics == [error]);
    }
}

@("reject actual parameters when no signature is defined")
unittest
{
    const source = `
        n = | '1' n.

        S: A <'1'>.
        A: 'a'.
        `.outdent.strip;
    const error = `
        no signature for affix parameters
        test.eag:3:6 S: A <'1'>.
                          ^
        `.outdent.strip;

    with (fixture())
    {
        parse(source).fail;

        assert(diagnostics == [error]);
    }
}

@("reject a variable without a defining position")
unittest
{
    const source = `
        n = | '1' n.

        S <+ n>:
            A <n>.
        A <- n>:
            'a'.
        `.outdent.strip;
    const error = `
        variable n never on defining position
        test.eag:3:6 S <+ n>:
                          ^
        `.outdent.strip;

    with (fixture())
    {
        parse(source).fail;

        assert(diagnostics == [error]);
    }
}

@("reject an unpaired unequal variable")
unittest
{
    const source = `
        n = | '1' n.

        S <- n>:
            A <!n1>.
        A <+ '1': n>:
            'a'.
        `.outdent.strip;
    const error = `
        variable n1 never on defining position
        test.eag:4:8     A <!n1>.
                            ^
        `.outdent.strip;

    with (fixture())
    {
        parse(source).fail;

        assert(diagnostics == [error]);
    }
}

@("reject an unequal variable without a defining position")
unittest
{
    const source = `
        n = | '1' n.

        S <- n1>:
            A <!n1>.
        A <- n>:
            'a'.
        `.outdent.strip;
    const error = `
        variable !n1 never on defining position
        test.eag:4:8     A <!n1>.
                            ^
        `.outdent.strip;

    with (fixture())
    {
        parse(source).fail;

        assert(diagnostics == [error]);
    }
}

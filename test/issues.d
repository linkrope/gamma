module test.issues;

import std.file;
import std.format;
import std.path;
import std.string;
import std.typecons : tuple;
import test.helper;

@("issue #1: grammar with unproductive start symbol")
unittest
{
    with (sandbox)
    {
        const name = buildPath(directory, "test.eag");
        const eag = `
            S = .

            S <+ : S>: A.
            A: 'a' A.
            `.outdent;

        write(name, eag);
        run!"%s --output-directory %s %s"(gamma, directory, name)
            .shouldFailWith("error: start symbol S is unproductive");
    }
}

@("issue #1: grammar with unproductive symbol but productive start symbol")
unittest
{
    with (sandbox)
    {
        const name = buildPath(directory, "test.eag");
        const eag = `
            S = .

            S <+ : S>: A | 'b'.
            A: 'a' A.
            `.outdent;

        write(name, eag);
        run!"%s --output-directory %s %s"(gamma, directory, name)
            .shouldPassWith("warn: A is unproductive");
    }
}

@("issue #11: do not silently skip trailing content")
unittest
{
    with (sandbox)
    {
        const name = buildPath(directory, "test.eag");
        const eag = `
            N = | '1' N.

            S<+  : N>:
                .
            S<+ '1' N: N>:
                'a' S<N> 'b'.
            `.outdent;

        write(name, eag);
        run!"%s --output-directory %s %s"(gamma, directory, name)
            .shouldPassWith("S grammar is SLAG");
        run!"cd %s && echo aa bbb | %s"(directory, dotSlash("S"))
            .shouldFailWith("syntax error, end expected");
    }
}

alias Example = tuple!("evaluator", "option", "result");

static foreach (example; [
    Example("SLAG", "", "grammar is SLAG"),
    Example("single-sweep", "--sweep", "grammar is single sweep"),
    Example("SOAG", "--soag", "grammar is SOAG"),
])
    @(format!"issue #6: %s predicate errors point to the checked identifier"(example.evaluator))
    unittest
    {
        import std.range : walkLength;
        import std.regex : matchAll, regex;

        with (sandbox)
        {
            const input = `
                DECL aa
                DECL aa

                APPL ab
                APPL ba
                `.outdent.strip;

            write(buildPath(directory, "input"), input);

            run!"%s %s --space %s --output-directory %s"(
                gamma, example.option, buildPath("example", "decl-appl.eag"), directory)
                .shouldPassWith(example.result);

            const result = run!"cd %s && %s input"(directory, dotSlash("DeclAppl"));

            result
                .shouldFailWith(
                    `error: predicate '?NotAlreadyDeclared'? failed\ninput:2:6 DECL aa`,
                    `error: predicate '?Declared'? failed\ninput:4:6 APPL ab`,
                    `error: predicate '?Declared'? failed\ninput:5:6 APPL ba`,
                );

            assert(result.output.matchAll(regex(`^error: predicate `, "m")).walkLength == 3, result.output);
        }
    }

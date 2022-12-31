module test.ell1;

import std.string;
import test.helper;

@("compile left-recursion.eag")
unittest
{
    with (sandbox)
    {
        run!"./gamma example/left-recursion.eag --output-directory %s"(directory)
            .shouldFailWith("left recursion");
    }
}

@("issue #11: disallow trailing content before EOF at LL(1) parser, by default")
unittest
{
    with (sandbox)
    {
        const eag = `
            NoEOF<+ 'Done': Done>: 'x'.
            Done = 'Done'.
            `.outdent;

        run!"cat <<EOF | ./gamma --output-directory %s%sEOF"(directory, eag)
            .shouldPassWith("NoEOF grammar is SLAG");
        run!"cd %s && echo x yy zzz | ./NoEOF"(directory)
            .shouldFailWith("syntax error, unexpected token\\(s\\) before end of file");    }
}

@("issue #11: allow trailing content before EOF at LL(1) parser if option -t has been passeed")
unittest
{
    with (sandbox)
    {
        const eag = `
            NoEOF<+ 'Done': Done>: 'x'.
            Done = 'Done'.
            `.outdent;

        run!"cat <<EOF | ./gamma --output-directory %s%sEOF"(directory, eag)
            .shouldPassWith("NoEOF grammar is SLAG");
        run!"cd %s && echo x yy zzz | ./NoEOF -t"(directory)
            .shouldPassWith("Done");
    }
}
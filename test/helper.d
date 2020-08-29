module test.helper;

import std.typecons;

alias Result = Tuple!(int, "status", string, "output");

Result run(string command)
{
    import std.process : executeShell;
    import std.stdio : writeln;

    writeln(command);
    return executeShell(command);
}

Result shouldMatch(Result result, string pattern)
{
    import std.regex : matchFirst, regex;

    with (result)
    {
        assert(status == 0, output);
        assert(output.matchFirst(regex(pattern, "m")), output);
    }
    return result;
}

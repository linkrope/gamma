module test.helper;

import std.typecons;

Sandbox sandbox()
{
    import std.format : format;
    import std.path : buildPath;

    __gshared size_t count = 0;

    synchronized
    {
        return Sandbox(buildPath("tmp", format!"%s"(count++)));
    }
}

private struct Sandbox
{
    const string directory;
}

alias Result = Tuple!(int, "status", string, "output");

Result run(string fmt, A...)(lazy A args)
{
    import std.format : format;
    import std.process : executeShell;
    import std.stdio : writeln;

    const command = format!fmt(args);

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

Result shouldFail(Result result, string pattern)
{
    import std.regex : matchFirst, regex;

    with (result)
    {
        assert(status != 0, output);
        assert(output.matchFirst(regex(pattern, "m")), output);
    }
    return result;
}

Result shouldFailNotMatching(Result result, string pattern)
{
    import std.regex : matchFirst, regex;

    with (result)
    {
        assert(status != 0, output);
        assert(!output.matchFirst(regex(pattern, "m")), output);
    }
    return result;
}

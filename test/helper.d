module test.helper;

import std.typecons;

Sandbox sandbox()
{
    import std.file : mkdirRecurse;
    import std.format : format;
    import std.path : buildPath;

    __gshared size_t count = 0;

    synchronized
    {
        const directory = buildPath("tmp", format!"%s"(count++));

        mkdirRecurse(directory);
        return Sandbox(directory);
    }
}

private struct Sandbox
{
    const string directory;

    const string gamma = dotSlash("gamma");
}

alias Result = Tuple!(int, "status", string, "output");

Result run(string fmt, A...)(lazy A args)
{
    import std.format : format;
    import std.process : executeShell;
    import std.stdio : writeln;

    auto command = format!fmt(args);

    writeln(command);
    return executeShell(command);
}

string dotSlash(string name)
{
    import std.path : buildPath;

    return buildPath(".", name);
}

Result shouldPassWith(Result result, string pattern)
{
    with (result)
    {
        assert(status == 0, output);
        assert(output.matches(pattern), output);
    }
    return result;
}

Result shouldFailWith(Result result, string pattern)
{
    with (result)
    {
        assert(status != 0, output);
        assert(output.matches(pattern), output);
    }
    return result;
}

bool matches(string input, string pattern)
{
    import std.regex : matchFirst, regex;

    return cast(bool) input.matchFirst(regex(pattern, "m"));
}

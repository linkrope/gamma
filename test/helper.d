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
}

alias Result = Tuple!(int, "status", string, "output");

Result run(string fmt, A...)(lazy A args)
{
    import std.format : format;
    import std.path : dirSeparator;
    import std.process : executeShell;
    import std.stdio : writeln;
    import std.string : translate;

    auto command = format!fmt(args).translate(['/': dirSeparator]);

    writeln(command);
    return executeShell(command);
}

Result shouldPassWith(Result result, string pattern)
{
    import std.regex : matchFirst, regex;

    with (result)
    {
        assert(status == 0, output);
        assert(output.matchFirst(regex(pattern, "m")), output);
    }
    return result;
}

Result shouldFailWith(Result result, string pattern)
{
    import std.regex : matchFirst, regex;

    with (result)
    {
        assert(status != 0, output);
        assert(output.matchFirst(regex(pattern, "m")), output);
    }
    return result;
}

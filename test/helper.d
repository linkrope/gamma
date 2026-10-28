module test.helper;

import std.range;
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

Result shouldPassWith(Result result, string[] patterns...)
in (!patterns.empty)
{
    with (result)
    {
        assert(status == 0, output);
        foreach (pattern; patterns)
            assert(output.matches(pattern), output);
    }
    return result;
}

Result shouldFailWith(Result result, string[] patterns...)
in (!patterns.empty)
{
    with (result)
    {
        assert(status != 0, output);
        foreach (pattern; patterns)
            assert(output.matches(pattern), output);
    }
    return result;
}

bool matches(string output, string pattern)
{
    import std.array : join;
    import std.regex : matchFirst, regex;
    import std.string : splitLines;

    // match diagnostic lines consistently regardless of the output's line endings.
    return cast(bool) output.splitLines.join("\n").matchFirst(regex(pattern, "m"));
}

string escape(string value)
{
    import std.array : array;
    import std.conv : to;
    import std.regex : escaper;

    return value.escaper.array.to!string;
}

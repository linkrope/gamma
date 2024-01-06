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

    auto command = format!fmt(args);

    version(Windows) 
    {
        import std.string : translate;
        dchar[dchar] translation = ['/': '\\'];
        command = translate(command, translation);

        import std.regex : regex, replaceAll, replaceFirst;
        command = replaceFirst(command, regex("echo\\s+\\|"), "echo. |");
        command = replaceAll(command, regex("\\bcat\\b"), "type");
    }

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

string asSingleLineDosInput(string multiLineInput) 
{
    import std.string : translate;

    string[dchar] translation = ['\n' : " ", '|' : "^|", '<' : "^<", '>' : "^>"];
    return translate(multiLineInput, translation);
}

/+ dub.sdl:
name "depend"
targetPath ".dub"
+/

import std;

private enum directories = ["src", "include", "unittest"];
private enum defaultArguments = ["--check", "tool/dependencies.puml"];

int main(string[] args)
{
    string[] arguments = ["dub", "run", "depend@0.4.0", "--"];

    if (args.length == 1)
        arguments ~= defaultArguments;
    else
        foreach (argument; args[1 .. $])
            if (argument != "--package")
                arguments ~= argument;

    appendSourcePaths(arguments);

    const result = execute(arguments);

    stdout.write(result.output);

    return result.status;
}

private void appendSourcePaths(ref string[] arguments)
{
    string[] sourcePaths = null;

    foreach (directory; directories)
        foreach (string path; dirEntries(directory, "*.d", SpanMode.depth))
            sourcePaths ~= path;

    arguments ~= sourcePaths.sort.array;
}

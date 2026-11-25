/+ dub.sdl:
name "dscanner"
targetPath ".dub"
+/

import std;

private enum directories = ["src", "test"];
private enum defaultArguments = ["--styleCheck"];

int main(string[] args)
{
    string[] arguments = ["dub", "run", "dscanner@0.15.2", "--"];

    if (args.length == 1)
        arguments ~= defaultArguments;
    else
        arguments ~= args[1 .. $];

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

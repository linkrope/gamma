/+ dub.sdl:
name "cogito"
targetPath ".dub"
+/

import std;

private enum directories = ["src", "include", "test", "unittest"];
private enum defaultArguments = [
    "--threshold", "15",
    "--module-threshold", "100",
    "--format", "flat",
    "--config", "tool/cogito.conf",
];

int main(string[] args)
{
    string[] arguments = ["dub", "run", "cogito@1.9.1", "--"];

    if (args.length == 1)
        arguments ~= defaultArguments;
    else
        arguments ~= args[1 .. $];

    foreach (directory; directories)
        foreach (string path; dirEntries(directory, "*.d", SpanMode.depth))
            arguments ~= path;

    const result = execute(arguments);

    stdout.write(result.output);

    return result.status;
}

/+ dub.sdl:
targetPath ".dub"
+/

import std;

private enum usage = `Usage: dub run --single tool/version.d -- [output-file]
Write the version to an optional output file.`;

// `git describe --always > build/version 2>/dev/null || printf '%s\n' "$DUB_PACKAGE_VERSION" > build/version`
// does not work on Windows
int main(string[] args)
{
    GetoptResult help;

    try
        help = getopt(args);
    catch (GetOptException error)
        return reportUsageError(error.msg);

    if (help.helpWanted)
    {
        defaultGetoptPrinter(usage, help.options);
        return 0;
    }

    if (args.length > 2)
        return reportUsageError();

    string version_ = environment.get("GITHUB_REF_NAME",
        environment.get("DUB_PACKAGE_VERSION", "unknown"));

    try
    {
        const result = execute(["git", "describe", "--tags", "--always"]);
        const checkoutVersion = result.output.strip;

        if (result.status == 0 && !checkoutVersion.empty)
            version_ = checkoutVersion;
    }
    catch (Exception)
    {
        // ignore
    }

    if (args.length > 1)
    {
        const path = args[1];
        const contents = version_ ~ "\n";

        // don't force DUB to relink targets when version is unchanged
        if (!path.exists || path.readText != contents)
        {
            mkdirRecurse(path.dirName);
            std.file.write(path, contents);
        }
    }
    else
        writeln(version_);

    return 0;
}

private int reportUsageError(string message = null)
{
    if (!message.empty)
        stderr.writeln(message);
    stderr.writeln(usage);
    return 1;
}

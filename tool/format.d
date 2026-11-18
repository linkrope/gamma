/+ dub.sdl:
name "format"
targetPath ".dub"
dependency "dfmt" repository="git+https://github.com/dlang-community/dfmt.git" version="c65d1c8a9cd2d784ded4cc7517c2cdd42c0c5c76"
subConfiguration "dfmt" "library"
+/

import dfmt.config : Config;
import dfmt.editorconfig : getConfigFor;
import dfmt.formatter : dfmtFormat = format;
import std;

private enum sourceDirectories = ["src", "unittest", "test", "include", "tool"];
private enum usage = `Usage: dub run --single tool/format.d -- [--check | --staged]
Without an option, format D source files in `
    ~ sourceDirectories.join(", ") ~ ".";

private enum Mode
{
    apply,
    check,
    staged,
}

int main(string[] args)
{
    bool check;
    bool staged;
    GetoptResult help;

    try
    {
        help = getopt(args,
            "check", "Check formatting without changing files.", &check,
            "staged", "Check formatting in the Git index.", &staged);
    }
    catch (GetOptException error)
        return reportUsageError(error.msg);

    if (help.helpWanted)
    {
        defaultGetoptPrinter(usage, help.options);
        return 0;
    }

    if (args.length != 1 || check && staged)
        return reportUsageError;

    const mode = staged ? Mode.staged : check ? Mode.check : Mode.apply;
    string[] unformatted;

    if (mode == Mode.staged)
        unformatted = checkStaged;
    else
        foreach (directory; sourceDirectories)
            foreach (string path; dirEntries(directory, "*.d", SpanMode.depth))
                if (formatFile(path, mode) && mode == Mode.check)
                    unformatted ~= path;

    if (!unformatted.empty)
    {
        reportUnformatted(unformatted);
        return 1;
    }

    return 0;
}

private bool formatFile(string path, Mode mode)
{
    const source = path.readText;
    const formatted = formatSource(path, source);
    const changed = formatted != source;

    if (changed && mode == Mode.apply)
        std.file.write(path, formatted);

    return changed;
}

private string[] checkStaged()
{
    string[] unformatted;

    foreach (path; stagedSourcePaths)
    {
        const source = gitOutput(["git", "show", ":" ~ path]);

        if (formatSource(path, source) != source)
            unformatted ~= path;
    }

    return unformatted;
}

private string[] stagedSourcePaths()
{
    string[] paths;
    const output = gitOutput(["git", "diff", "--cached", "--name-only", "--diff-filter=ACMR", "-z"]);

    foreach (path; output.split('\0'))
        if (!path.empty && isSourcePath(path))
            paths ~= path;

    return paths;
}

private bool isSourcePath(string path)
{
    if (!path.endsWith(".d"))
        return false;

    foreach (directory; sourceDirectories)
        if (path.startsWith(directory ~ "/"))
            return true;

    return false;
}

private string gitOutput(string[] arguments)
{
    const result = execute(arguments);

    enforce(result.status == 0,
        "tool/format: --staged requires a Git checkout");

    return result.output;
}

private string formatSource(string path, string source)
{
    auto output = appender!string;
    auto config = configFor(path);

    enforce(dfmtFormat(path, cast(ubyte[]) source.dup, output, &config),
        "dfmt: unable to format " ~ path);

    return output.data;
}

private void reportUnformatted(string[] paths)
{
    foreach (path; paths)
        stderr.writeln("dfmt: ", path, " is not formatted; run: dub run --single tool/format.d --");
}

private int reportUsageError(string message = null)
{
    if (!message.empty)
        stderr.writeln(message);
    stderr.writeln(usage);

    return 1;
}

private Config configFor(string path)
{
    Config config;

    config.initializeWithDefaults;

    auto fileConfig = getConfigFor!Config(path);

    fileConfig.pattern = "*.d";
    config.merge(fileConfig, path);

    return config;
}

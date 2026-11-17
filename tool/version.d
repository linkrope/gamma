/+ dub.sdl:
+/

import std.file : mkdirRecurse, write;
import std.path : dirName;
import std.process : environment, execute;
import std.range : empty;
import std.stdio : writeln;
import std.string : strip;

// `git describe --always > build/version 2>/dev/null || printf '%s\n' "$DUB_PACKAGE_VERSION" > build/version`
// does not work on Windows
void main(string[] args)
{
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

        mkdirRecurse(path.dirName);
        path.write(version_ ~ "\n");
    }
    else
        writeln(version_);
}

import std;

void main(string[] args)
{
    enforce(args.length == 2, "expected an output path");

    const path = args[1];
    const packageVersion = environment.get("DUB_PACKAGE_VERSION", "unknown") ~ "\n";

    if (!path.exists || path.readText != packageVersion)
    {
        mkdirRecurse(path.dirName);
        std.file.write(path, packageVersion);
    }
}

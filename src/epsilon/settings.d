module epsilon.settings;

struct Settings
{
    /// DISABLE collapsing constant trees
    bool c;

    /// DISABLE optimizing of variable storage in compiled compiler
    bool o;

    /// parser IGNORES regular token marks at hyper-nonterminals
    bool p;

    /// DISABLE reference counting in compiled compiler
    bool r;

    /// use space instead of newline as separator
    bool space;

    /// write compilation output as default
    bool write;

    string outputDirectory; // FIXME: import table files in executable

    string tempDirectory;

    string outputPath(string fileName) nothrow pure @safe
    {
        import std.path : buildPath;
        import std.range : empty;

        return buildPath(outputDirectory.empty ? "." : outputDirectory, fileName);
    }

    string path(string fileName) nothrow pure @safe
    {
        import std.path : buildPath;

        return buildPath(tempDirectory, fileName);
    }
}

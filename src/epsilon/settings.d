module epsilon.settings;

struct Settings
{
    /// DISABLE collapsing constant trees
    bool c;

    /// debug reference counting
    bool dR;

    /// show modules, don't compile
    bool showMod;

    /// DISABLE optimizing of variable storage in compiled compiler
    bool o;

    /// parser IGNORES regular token marks at hyper-nonterminals
    bool p;

    /// DISABLE reference counting in compiled compiler
    bool r;

    /// use space instead of newline as separator
    bool space;

    /// print debug output
    bool verbose;

    /// write compilation output as default
    bool write;

    /// compile single-sweep evaluator
    bool sweep;

    /// compile SOAG evaluator
    bool soag;

    string outputDirectory;

    string path(string fileName) nothrow pure @safe
    {
        import std.path : buildPath;
        import std.range : empty;

        if (outputDirectory.empty)
            return fileName;
        return buildPath(outputDirectory, fileName);
    }
}

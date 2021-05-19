module epsilon.settings;

struct Settings
{
    /// DISABLE collapsing constant trees
    bool c;

    /// generate only, do not compile
    bool generate;

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

    /// generate SLAG evaluator
    bool slag;

    /// generate single-sweep evaluator
    bool sweep;

    /// generate SOAG evaluator
    bool soag;

    /// report offset for positions instead of line and column (needed by the Epsilon language server) 
    bool lsSupport;

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

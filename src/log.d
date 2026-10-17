module log;

import std.stdio;

alias trace = log!(Level.trace);
alias info = log!(Level.info);
alias warn = log!(Level.warn);
alias error = log!(Level.error);
alias fatal = log!(Level.fatal);

template log(Level level)
{
    void log(string fmt, string file = __FILE__, size_t line = __LINE__, A...)(lazy A args)
    {
        import std.format : format;

        if (level & levels)
            logger.log(level, file, line, format!fmt(args));
    }
}

static this()
{
    version (unittest)
        logger = TestLogger.init;
    else
        logger = Logger(stderr);
    levels = Level.info | Level.warn | Level.error | Level.fatal;
}

version (unittest)
    TestLogger logger;
else
    Logger logger;

struct Logger
{
    private File file;

    this(File file)
    {
        this.file = file;
    }

    void log(Level level, string file, size_t line, string message) @safe
    {
        import std.conv : to;

        auto writer = this.file.lockingTextWriter;

        writer.put(level.to!string);
        writer.put(": ");
        writer.put(message);
        writer.put('\n');
    }
}

version (unittest)
{
    struct TestLogger
    {
        struct Entry
        {
            Level level;
            string file;
            size_t line;
            string message;
        }

        Entry[] entries;

        void log(Level level, string file, size_t line, string message) @safe
        {
            this.entries ~= Entry(level, file, line, message);
        }

        void clear() @safe
        {
            this.entries = null;
        }
    }
}

uint levels;

enum Level
{
    trace = 1, // detailed tracing
    info = 2, // useful information
    warn = 4, // potential problem
    error = 8, // recoverable error
    fatal = 16, // fatal failure
}

@("record and clear enabled log entries")
unittest
{
    const previousLevels = levels;
    scope (exit) levels = previousLevels;
    levels = Level.error;
    logger.clear;
    scope (exit) logger.clear;

    trace!"filtered";
    error!"test %s"("message");

    assert(logger.entries.length == 1);
    assert(logger.entries[0].level == Level.error);
    assert(logger.entries[0].message == "test message");
    assert(logger.entries[0].file.length > 0 && logger.entries[0].line > 0);
    logger.clear;
    assert(logger.entries.length == 0);
}

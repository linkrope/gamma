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
    logger = Logger(stderr);
    levels = Level.info | Level.warn | Level.error | Level.fatal;
}

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

uint levels;

enum Level
{
    trace = 1, // detailed tracing
    info = 2, // useful information
    warn = 4, // potential problem
    error = 8, // recoverable error
    fatal = 16, // fatal failure
}

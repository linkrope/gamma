module gamma.parsgen.lalr1.FixWriter;

import io : Input;
import std.exception : enforce;
import std.stdio : File;

public void includeFix(ref Input fix, File output, char terminator, string fixName)
{
    while (fix.front != terminator)
    {
        enforce(fix.front != 0, "unexpected end of " ~ fixName);
        output.write(fix.front);
        fix.popFront;
    }
    fix.popFront;
}

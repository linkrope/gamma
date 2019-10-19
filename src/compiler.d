module compiler;

import IO = eIO;
import scanner = eScanner;
import std.stdio;

void main(string[] args)
{
    import std.file : readText;
    import std.format : format;

    auto buffer = new char[256];
    foreach (arg; args[1 .. $])
    {
        auto input = new IO.TextIn(readText!(char[])(arg));
        scanner.Init(input);
        char tok;
        do
        {
            scanner.Get(tok);
            if (tok == scanner.ide || tok == scanner.str)
            {
                write((tok == scanner.ide) ? "ide" : "str");
                write(format!"[%s] = "(scanner.Val));
                scanner.WriteRepr(IO.Msg, scanner.Val);
                IO.Update(IO.Msg);
                writeln;
            }
            else if (tok == scanner.num)
                writeln("num = ", scanner.Val);
            else
                writeln(tok);
        }
        while (tok != scanner.eot);
    }
}

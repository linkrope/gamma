import std.stdio;

void main(string[] args)
{
    import std.range : dropOne, empty;

    if (args.dropOne.empty)
        compile(stdin);

    foreach (arg; args.dropOne)
        compile(File(arg));
}

void compile(File file)
{
    import IO = eIO;
    import Scan = OberonOScan;

    auto In = new IO.TextIn(file);

    Scan.Init(In);

    int Tok;

    do
    {
        Scan.Get(Tok);
        Scan.WriteRepr(IO.Msg, Tok);
        IO.WriteLn(IO.Msg);
    }
    while (Tok != 0);
    IO.Update(IO.Msg);
}

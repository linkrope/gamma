module epsilon;

import Analyser = eAnalyser;

void main(string[] args)
{
    import std.range : dropOne;

    foreach (arg; args.dropOne)
    {
        Analyser.Analyse(arg);
        Analyser.Warnings;
    }
}

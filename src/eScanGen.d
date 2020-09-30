module eScanGen;

import EAG = eEAG;
import IO = eIO;
import Scanner = eScanner;
import Sets = eSets;
import io : TextIn;
import log;
import runtime;

const firstUserTok = 3;
const lenOfPredefinedToken = 8;
bool[256] IsIdent;
bool[256] IsSymbol;

void Generate()
{
    TextIn Fix;
    IO.TextOut Mod;
    int Term;
    int MaxTokLen;
    int Len;
    string name;
    bool Error;
    bool ShowMod;

    void TestToken(string Str, ref int Len)
    {
        import std.string : toStringz;

        int i;

        void Err(string Msg)
        {
            Error = true;
            error!"token %s - %s"(Str, Msg);
        }

        const s = Str.toStringz;

        Len = 0;
        if (s[0] != '\'' && s[0] != '"' || s[1] == 0 || s[1] == s[0])
        {
            Err("must be non empty string");
            return;
        }
        if (s[1] == '\'' || s[1] == '"' || s[1] == ' ')
        {
            i = 2;
        }
        else if (s[1] == '\\')
        {
            i = 3;
        }
        else if (IsIdent[s[1]])
        {
            i = 2;
            while (IsIdent[s[i]])
            {
                ++i;
            }
        }
        else if (IsSymbol[s[1]])
        {
            i = 2;
            while (IsSymbol[s[i]])
            {
                ++i;
            }
        }
        else
        {
            Err("contains illegal char");
            return;
        }
        if (s[i] != s[0] || s[i + 1] != 0)
        {
            Err("contains illegal char");
            return;
        }
        Len = i - 1;
    }

    void InclFix(char Term)
    {
        import std.conv : to;
        import std.exception : enforce;

        char c = Fix.front.to!char;

        while (c != Term)
        {
            enforce(c != 0,
                    "error: unexpected end of eScanGen.fix.d");

            Mod.write(c);
            Fix.popFront;
            c = Fix.front.to!char;
        }
        Fix.popFront;
    }

    ShowMod = IO.IsOption('m');
    info!"ScanGen writing %s"(EAG.BaseName);
    if (EAG.Performed(Sets.SET(EAG.analysed)))
    {
        Error = false;
        MaxTokLen = lenOfPredefinedToken;
        for (Term = EAG.firstHTerm; Term <= EAG.NextHTerm - 1; ++Term)
        {
            const Str = Scanner.repr(EAG.HTerm[Term].Id);

            TestToken(Str, Len);
            if (Len > MaxTokLen)
                MaxTokLen = Len;
        }
        if (!Error)
        {
            Fix = TextIn("fix/eScanGen.fix.d");
            name = EAG.BaseName ~ "Scan";
            Mod = new IO.TextOut(name ~ ".d");
            InclFix('$');
            Mod.write(name);
            InclFix('$');
            Mod.write(MaxTokLen + 1);
            InclFix('$');
            Mod.write(EAG.NextHTerm - EAG.firstHTerm + firstUserTok);
            InclFix('$');
            for (Term = EAG.firstHTerm; Term <= EAG.NextHTerm - 1; ++Term)
            {
                Mod.write("    Enter(");
                Mod.write(Term - EAG.firstHTerm + firstUserTok);
                Mod.write(", ");
                Mod.write(Scanner.repr(EAG.HTerm[Term].Id));
                Mod.write(");\n");
            }
            InclFix('$');
            Mod.write(name);
            InclFix('$');
            Mod.flush;
            if (ShowMod)
            {
                IO.Show(Mod);
                IO.Msg.writeln;
            }
            else
            {
                IO.Compile(Mod);
            }
            IO.CloseOut(Mod);
        }
    }
}

static this()
{
    for (int i = 0; i < IsIdent.length; ++i)
    {
        IsIdent[i] = false;
    }
    for (int i = 'A'; i <= 'Z'; ++i)
    {
        IsIdent[i] = true;
    }
    for (int i = 'a'; i <= 'z'; ++i)
    {
        IsIdent[i] = true;
    }
    for (int i = '0'; i <= '9'; ++i)
    {
        IsIdent[i] = true;
    }
    for (int i = 0; i <= ' '; ++i)
    {
        IsSymbol[i] = false;
    }
    for (int i = ' ' + 1; i < IsSymbol.length; ++i)
    {
        IsSymbol[i] = !IsIdent[i];
    }
    IsSymbol['\''] = false;
    IsSymbol['"'] = false;
}

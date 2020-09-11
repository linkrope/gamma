module eScanGen;

import runtime;
import IO = eIO;
import Scanner = eScanner;
import Sets = eSets;
import EAG = eEAG;
import io : TextIn;

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
    char[] Str = new char[400];
    char[] Name = new char[EAG.BaseNameLen + 10];
    bool Error;
    bool CompileError;
    bool ShowMod;

    void TestToken(ref char[] s, ref int Len)
    {
        int i;

        void Err(string Msg)
        {
            int i = 0;

            Error = true;
            IO.WriteText(IO.Msg, "\n  error in token: ");
            while (s[i] != 0)
            {
                IO.Write(IO.Msg, s[i]);
                ++i;
            }
            IO.WriteString(IO.Msg, " - ");
            IO.WriteText(IO.Msg, Msg);
            IO.Update(IO.Msg);
        }

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

            IO.Write(Mod, c);
            Fix.popFront;
            c = Fix.front.to!char;
        }
        Fix.popFront;
    }

    void Append(ref char[] Dest, char[] Src, string Suf)
    {
        int i;
        int j;
        i = 0;
        j = 0;

        while (Src[i] != 0 && i + 1 < Dest.length)
        {
            Dest[i] = Src[i];
            ++i;
        }
        while (j < Suf.length && i + 1 < Dest.length)
        {
            Dest[i] = Suf[j];
            ++i;
            ++j;
        }
        Dest[i] = 0;
    }

    ShowMod = IO.IsOption('m');
    IO.WriteString(IO.Msg, "ScanGen writing ");
    IO.WriteString(IO.Msg, EAG.BaseName);
    IO.WriteString(IO.Msg, "   ");
    IO.Update(IO.Msg);
    if (EAG.Performed(Sets.SET(EAG.analysed)))
    {
        Error = false;
        MaxTokLen = lenOfPredefinedToken;
        for (Term = EAG.firstHTerm; Term <= EAG.NextHTerm - 1; ++Term)
        {
            Scanner.GetRepr(EAG.HTerm[Term].Id, Str);
            TestToken(Str, Len);
            if (Len > MaxTokLen)
            {
                MaxTokLen = Len;
            }
        }
        if (!Error)
        {
            Fix = TextIn("fix/eScanGen.fix.d");
            Append(Name, EAG.BaseName, "Scan");
            IO.CreateModOut(Mod, Name);
            InclFix('$');
            IO.WriteString(Mod, Name);
            InclFix('$');
            IO.WriteInt(Mod, MaxTokLen + 1);
            InclFix('$');
            IO.WriteInt(Mod, EAG.NextHTerm - EAG.firstHTerm + firstUserTok);
            InclFix('$');
            for (Term = EAG.firstHTerm; Term <= EAG.NextHTerm - 1; ++Term)
            {
                IO.WriteText(Mod, "    Enter(");
                IO.WriteInt(Mod, Term - EAG.firstHTerm + firstUserTok);
                IO.WriteText(Mod, ", ");
                Scanner.WriteRepr(Mod, EAG.HTerm[Term].Id);
                IO.WriteText(Mod, ");\n");
            }
            InclFix('$');
            IO.WriteString(Mod, Name);
            InclFix('$');
            IO.Update(Mod);
            if (ShowMod)
            {
                IO.Show(Mod);
                IO.WriteLn(IO.Msg);
            }
            else
            {
                IO.Compile(Mod, CompileError);
                if (CompileError)
                {
                    IO.Show(Mod);
                }
            }
            IO.CloseOut(Mod);
        }
        else
        {
            IO.WriteLn(IO.Msg);
        }
    }
    else
    {
        IO.WriteLn(IO.Msg);
    }
    IO.Update(IO.Msg);
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

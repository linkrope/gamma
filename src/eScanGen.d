module eScanGen;

import runtime;
import IO = eIO;
import Scanner = eScanner;
import EAG = eEAG;

const firstUserTok = 3;
const lenOfPredefinedToken = 8;
bool[256] IsIdent;
bool[256] IsSymbol;
int i;

void Generate()
{
    IO.TextIn Fix;
    IO.TextOut Mod;
    int Term;
    int MaxTokLen;
    int Len;
    char[] Str = new char[400];
    char[] Name = new char[EAG.BaseNameLen + 10];
    bool Error;
    bool OpenError;
    bool CompileError;
    bool ShowMod;

    void TestToken(ref char[] s, ref int Len)
    {
        int i;
        void Err(string Msg)
        {
            int i;
            Error = true;
            IO.WriteText(IO.Msg, "\n  error in token: ");
            i = 0;
            while (s[i] != '\x00')
            {
                IO.Write(IO.Msg, s[i]);
                ++i;
            }
            IO.WriteString(IO.Msg, " - ");
            IO.WriteText(IO.Msg, Msg);
            IO.Update(IO.Msg);
        }

        Len = 0;
        if (s[0] != '\'' && s[0] != '"' || s[1] == '\x00' || s[1] == s[0])
        {
            Err("must be non empty string");
            return;
        }
        if (s[1] == '\'' || s[1] == '"' || s[1] == ' ')
        {
            i = 2;
        }
        else if (IsIdent[ORD(s[1])])
        {
            i = 2;
            while (IsIdent[ORD(s[i])])
            {
                ++i;
            }
        }
        else if (IsSymbol[ORD(s[1])])
        {
            i = 2;
            while (IsSymbol[ORD(s[i])])
            {
                ++i;
            }
        }
        else
        {
            Err("contains illegal char");
            return;
        }
        if (s[i] != s[0] || s[i + 1] != '\x00')
        {
            Err("contains illegal char");
            return;
        }
        Len = i - 1;
    }

    void InclFix(char Term)
    {
        char c;
        IO.Read(Fix, c);
        while (c != Term)
        {
            if (c == '\x00')
            {
                throw new Exception("error: unexpected end of eScanGen.Fix");
            }
            IO.Write(Mod, c);
            IO.Read(Fix, c);
        }
    }

    void Append(ref char[] Dest, char[] Src, string Suf)
    {
        int i;
        int j;
        i = 0;
        j = 0;
        while (Src[i] != '\x00' && i < Dest.length - 1)
        {
            Dest[i] = Src[i];
            ++i;
        }
        while (j < Suf.length && i < Dest.length - 1)
        {
            Dest[i] = Suf[j];
            ++i;
            ++j;
        }
        Dest[i] = '\x00';
    }

    ShowMod = IO.IsOption('m');
    IO.WriteString(IO.Msg, "ScanGen writing ");
    IO.WriteString(IO.Msg, EAG.BaseName);
    IO.WriteString(IO.Msg, "   ");
    IO.Update(IO.Msg);
    if (EAG.Performed(SET(1 << EAG.analysed)))
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
            IO.OpenIn(Fix, "fix/eScanGen.fix.d", OpenError);
            if (OpenError)
            {
                throw new Exception("error: cannot open eScanGen.Fix");
            }
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
            IO.CloseIn(Fix);
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
    for (i = 0; i <= IsIdent.length - 1; ++i)
    {
        IsIdent[i] = false;
    }
    for (i = ORD('A'); i <= ORD('Z'); ++i)
    {
        IsIdent[i] = true;
    }
    for (i = ORD('a'); i <= ORD('z'); ++i)
    {
        IsIdent[i] = true;
    }
    for (i = ORD('0'); i <= ORD('9'); ++i)
    {
        IsIdent[i] = true;
    }
    for (i = 0; i <= ORD(' '); ++i)
    {
        IsSymbol[i] = false;
    }
    for (i = ORD(' ') + 1; i <= IsSymbol.length - 1; ++i)
    {
        IsSymbol[i] = !IsIdent[i];
    }
    IsSymbol[ORD('\'')] = false;
    IsSymbol[ORD('"')] = false;
}

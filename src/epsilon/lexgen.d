module epsilon.lexgen;

import EAG = epsilon.eag;
import epsilon.settings;
import io : Input, read;
import log;
import runtime;
import std.stdio;

private const firstUserTok = 3;
private const lenOfPredefinedToken = 8;
private bool[256] IsIdent;
private bool[256] IsSymbol;

public string Generate(Settings settings)
in (EAG.Performed(EAG.analysed))
{
    Input Fix;
    File output;
    int Term;
    int MaxTokLen;
    int Len;
    bool Error;

    void TestToken(string Str, ref int Len)
    {
        import std.string : toStringz;

        int i;

        void Err(string Msg)
        {
            Error = true;
            error!"token %s %s"(Str, Msg);
        }

        const s = Str.toStringz;

        Len = 0;
        if (s[0] != '\'' && s[0] != '"' && s[0] != '`' || s[1] == 0 || s[1] == s[0])
        {
            Err("must be non empty string");
            return;
        }
        if (s[1] == '\'' || s[1] == '"' || s[1] == '`' || s[1] == ' ')
        {
            i = 2;
        }
        else if ((s[0] == '\'' || s[0] == '"') && s[1] == '\\')
        {
            i = 3;
        }
        else if (s[0] == '`' && s[1] == '\\')
        {
            i = 2;
        }
        else if (IsIdent[s[1]])
        {
            i = 2;
            while (IsIdent[s[i]])
                ++i;
        }
        else if (IsSymbol[s[1]])
        {
            i = 2;
            while (IsSymbol[s[i]])
                ++i;
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
                    "error: unexpected end of lexgen.fix.d");

            output.write(c);
            Fix.popFront;
            c = Fix.front.to!char;
        }
        Fix.popFront;
    }

    info!"LexGen writing %s"(EAG.BaseName);
    Error = false;
    MaxTokLen = lenOfPredefinedToken;
    for (Term = EAG.firstHTerm; Term < EAG.NextHTerm; ++Term)
    {
        const Str = EAG.symbolTable.symbol(EAG.HTerm[Term].Id);

        TestToken(Str, Len);
        if (Len > MaxTokLen)
            MaxTokLen = Len;
    }
    if (Error)
        assert(0, "TODO: error handling for lexer generator");

    enum fixName = "lexgen.fix.d";
    const name = EAG.BaseName ~ "Lex";
    const fileName = settings.path(name ~ ".d");

    Fix = Input(fixName, import(fixName));
    output = File(fileName, "w");
    InclFix('$');
    output.write(name);
    InclFix('$');
    output.write(MaxTokLen + 1);
    InclFix('$');
    output.write(EAG.NextHTerm - EAG.firstHTerm + firstUserTok);
    InclFix('$');
    for (Term = EAG.firstHTerm; Term < EAG.NextHTerm; ++Term)
        output.writeln("Enter(", Term - EAG.firstHTerm + firstUserTok, ", ", EAG.HTerm[Term].Id.repr, ");");
    InclFix('$');
    output.write(name);
    InclFix('$');
    output.close;
    return fileName;
}

private string repr(int id)
{
    import std.range : dropBackOne, dropOne, front, only;
    import std.format : format;

    const value = EAG.symbolTable.symbol(id);

    if (value.front == '\'')
    {
        return format!"%(%s%)"(only(value.dropOne.dropBackOne));
    }
    return value;

}

static this() @nogc nothrow @safe
{
    for (int i = 0; i < IsIdent.length; ++i)
        IsIdent[i] = false;
    for (int i = 'A'; i <= 'Z'; ++i)
        IsIdent[i] = true;
    for (int i = 'a'; i <= 'z'; ++i)
        IsIdent[i] = true;
    for (int i = '0'; i <= '9'; ++i)
        IsIdent[i] = true;
    for (int i = 0; i <= ' '; ++i)
        IsSymbol[i] = false;
    for (int i = ' ' + 1; i < IsSymbol.length; ++i)
        IsSymbol[i] = !IsIdent[i];
    IsSymbol['\''] = false;
    IsSymbol['"'] = false;
    IsSymbol['`'] = false;
}

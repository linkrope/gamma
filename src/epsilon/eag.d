module epsilon.eag;

import io : Position;
import runtime;
import std.algorithm;
import std.bitmanip;
import symbols : SymbolTable;

struct EAG
{
    enum nil = 0;
    enum empty = 0;
    enum firstParam = 0;
    enum firstHAlt = 0;
    enum firstHFactor = 0;

    enum
    {
        analysed = 1 << 0,
        predicates = 1 << 1,
        parsable = 1 << 2,
        isSLAG = 1 << 3,
        isSweep = 1 << 4,
        hasEvaluator = 1 << 5,
    }

    struct ParamsDesc
    {
        int Params;
        Position Pos;

        public string toString() const @safe
        {
            import std.format : format;

            return format!"Params(%-(%s, %))"(params(eag));
        }

        ParamRecord[] params(ref EAG eag) const nothrow @safe
        {
            const length = eag.ParamBuf[Params .. $]
                .map!"a.Affixform"
                .countUntil(nil);

            return eag.ParamBuf[Params .. Params + length];
        }
    }

    struct ParamRecord
    {
        int Affixform;
        Position Pos;
        bool isDef;

        public string toString() const pure @safe
        {
            import std.format : format;

            if (Affixform == nil)
                return "Param()";
            return format!"Param(%s, %s)"(isDef ? "def" : "app", Affixform);
        }
    }

    enum firstNode = 1;
    enum firstVar = 1;

    struct ScopeDesc
    {
        int Beg;
        int End;

        public string toString() const pure @safe
        {
            import std.format : format;

            return format!"Scope(Beg=%s, End=%s)"(Beg, End);
        }
    }

    struct VarRecord
    {
        int Sym;
        int Num;
        int Neg;
        Position Pos;
        bool Def;

        public string toString() const @safe
        {
            import std.format : format;

            return format!"Variable(Sym=%s, Num=%s, Neg=%s, Def=%s)\n%s"(Sym, Num, Neg, Def, Pos);
        }
    }

    class Rule
    {
        Alt Sub;
    }

    class Alt
    {
        int Ind;
        int Up;
        Alt Next;
        Factor Sub;
        Factor Last;
        ParamsDesc Formal;
        ParamsDesc Actual;
        ScopeDesc Scope;
        Position Pos;

        public override string toString() const @safe
        {
            import std.format : format;

            string[] items;

            items ~= format!"Ind=%s"(Ind);
            items ~= format!"Up=%s"(Up);
            // TODO: Next, Sub, Last
            items ~= format!"Formal=%s"(Formal);
            items ~= format!"Actual=%s"(Actual);
            items ~= Scope.toString;
            return format!"Alt(%-(%s, %))"(items);
        }
    }

    static void assign(Alt lhs, Alt rhs) @nogc nothrow pure @safe
    in (lhs !is null)
    in (rhs !is null)
    {
        lhs.Ind = rhs.Ind;
        lhs.Up = rhs.Up;
        lhs.Next = rhs.Next;
        lhs.Sub = rhs.Sub;
        lhs.Last = rhs.Last;
        lhs.Formal = rhs.Formal;
        lhs.Actual = rhs.Actual;
        lhs.Scope = rhs.Scope;
        lhs.Pos = rhs.Pos;
    }

    class Grp : Rule
    {
    }

    class Opt : Rule
    {
        Position EmptyAltPos;
        ScopeDesc Scope;
        ParamsDesc Formal;
    }

    class Rep : Rule
    {
        Position EmptyAltPos;
        ScopeDesc Scope;
        ParamsDesc Formal;
    }

    class Factor
    {
        int Ind;
        Factor Prev;
        Factor Next;
    }

    class Term : Factor
    {
        int Sym;
        Position Pos;
    }

    class Nont : Factor
    {
        int Sym;
        ParamsDesc Actual;
        Position Pos;

    }

    static void assign(Nont lhs, Nont rhs) @nogc nothrow pure @safe
    in (lhs !is null)
    in (rhs !is null)
    {
        lhs.Ind = rhs.Ind;
        lhs.Prev = rhs.Prev;
        lhs.Next = rhs.Next;
        lhs.Sym = rhs.Sym;
        lhs.Actual = rhs.Actual;
        lhs.Pos = rhs.Pos;
    }

    enum firstDom = 0;
    enum firstMAlt = 1;
    enum firstMemb = 1;

    struct MAltRecord
    {
        int Left;
        int Right;
        int Arity;
        int Next;
    }

    enum firstMTerm = 1;
    enum firstMNont = 1;
    enum firstHTerm = 0;
    enum firstHNont = 0;

    struct MTermRecord
    {
        int Id;
    }

    struct MNontRecord
    {
        int Id;
        int MRule;
        int Last;
        bool IsToken;
    }

    struct HTermRecord
    {
        int Id;
    }

    struct HNontRecord
    {
        int Id;
        int NamedId;
        int Sig;
        Rule Def;
        bool IsToken;

        bool anonymous() const @nogc nothrow pure @safe
        {
            return Id < 0;
        }
    }

    ParamRecord[] ParamBuf;
    int NextParam;
    int[] NodeBuf;
    int NextNode;
    VarRecord[] Var;
    int NextVar;
    int Scope;
    int NextHAlt;
    int NextHFactor;
    int NontCount;
    int[] DomBuf;
    int NextDom;
    MAltRecord[] MAlt;
    int NextMAlt;
    int MaxMArity;
    int[] MembBuf;
    int NextMemb;
    MTermRecord[] MTerm;
    int NextMTerm;
    MNontRecord[] MNont;
    int NextMNont;
    HTermRecord[] HTerm;
    int NextHTerm;
    HNontRecord[] HNont;
    int NextHNont;

    // HNont can contain gaps, so All identifies its valid entries.
    BitArray All;
    BitArray Prod;
    BitArray Reach;
    BitArray Null;
    BitArray Pred;
    int StartSym;
    string BaseName;
    SymbolTable symbolTable;

void AppParam(int Affixform, Position Pos) nothrow @safe
{
    ParamBuf.length = NextParam;
    ParamBuf ~= ParamRecord(Affixform, Pos, false);
    NextParam = cast(int) ParamBuf.length;
}

void AppDom(char Dir, int Dom) nothrow @safe
{
    if (Dir == '-')
        Dom = -Dom;
    DomBuf.length = NextDom;
    DomBuf ~= Dom;
    NextDom = cast(int) DomBuf.length;
}

int NewMAlt(int Sym, int Right) nothrow @safe
{
    int Arity;
    int i;

    MAlt.length = NextMAlt;
    const alt = NextMAlt;

    if (MNont[Sym].MRule == nil)
        MNont[Sym].MRule = alt;
    else
        MAlt[MNont[Sym].Last].Next = alt;
    MNont[Sym].Last = alt;
    i = Right;
    Arity = 0;
    while (MembBuf[i] != 0)
    {
        if (MembBuf[i] > 0)
            ++Arity;
        ++i;
    }
    if (Arity > MaxMArity)
        MaxMArity = Arity;
    MAlt ~= MAltRecord(Sym, Right, Arity, nil);
    NextMAlt = cast(int) MAlt.length;
    return alt;
}

void AppMemb(int Val) nothrow @safe
{
    MembBuf.length = NextMemb;
    MembBuf ~= Val;
    NextMemb = cast(int) MembBuf.length;
}

void AppNode(int Val) nothrow @safe
{
    NodeBuf.length = NextNode;
    NodeBuf ~= Val;
    NextNode = cast(int) NodeBuf.length;
}

int FindVar(int Sym, int Num, Position Pos, bool Def) nothrow @safe
{
    int V = Scope;

    while (V < NextVar && (Var[V].Sym != Sym || Var[V].Num != Num))
        ++V;
    if (V == NextVar)
    {
        V = Scope;
        while (V < NextVar && (Var[V].Sym != Sym || Var[V].Num != -Num))
            ++V;
        if (V != NextVar)
        {
            Var[V].Neg = NextVar;
        }
        Var.length = NextVar;
        Var ~= VarRecord(Sym, Num, V == NextVar ? nil : V, Pos, Def);
        V = NextVar;
        NextVar = cast(int) Var.length;
    }
    else
    {
        Var[V].Def = Var[V].Def || Def;
    }
    return V;
}

public string HTermRepr(int Term) @nogc nothrow @safe
{
    return symbolTable.symbol(HTerm[Term].Id);
}

public string HNontRepr(size_t Nont) @safe
{
    import std.format : format;

    if (HNont[Nont].anonymous)
        return format!"A%s"(-HNont[Nont].Id);
    return symbolTable.symbol(HNont[Nont].Id);
}

public string VarRepr(int V) nothrow @safe
{
    import std.math : abs;

    string result;

    if (Var[V].Num < 0)
        result ~= '!';
    result ~= symbolTable.symbol(MNont[Var[V].Sym].Id);
    if (abs(Var[V].Num) > 1)
        result ~= symbolTable.symbol(abs(Var[V].Num) - 2);
    return result;
}

public string NamedHNontRepr(size_t Nont) @nogc nothrow @safe
{
    return symbolTable.symbol(HNont[Nont].NamedId);
}

}

// Transitional legacy instance. Generator entry points will receive EAG explicitly.
EAG eag;

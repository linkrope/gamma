module epsilon.eag;

import io : Position, UndefPos;
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
    int NOAlt;
    int NOTerm;
    int NONont;
    int NOOpt;
    int NORep;
    int NOGrp;
    int[] DomBuf;
    int NextDom;
    int CurSig;
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
    int NextAnonym;

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

int FindMTerm(int Id) nothrow @safe
{
    foreach (sym; firstMTerm .. cast(int) MTerm.length)
        if (MTerm[sym].Id == Id)
            return sym;
    MTerm.length = NextMTerm;
    MTerm ~= MTermRecord(Id);
    NextMTerm = cast(int) MTerm.length;
    return NextMTerm - 1;
}

int FindMNont(int Id) nothrow @safe
{
    foreach (sym; firstMNont .. cast(int) MNont.length)
        if (MNont[sym].Id == Id)
            return sym;
    MNont.length = NextMNont;
    MNont ~= MNontRecord(Id, nil, nil, false);
    NextMNont = cast(int) MNont.length;
    return NextMNont - 1;
}

int FindHTerm(int Id) nothrow @safe
{
    foreach (sym; firstHTerm .. cast(int) HTerm.length)
        if (HTerm[sym].Id == Id)
            return sym;
    HTerm.length = NextHTerm;
    HTerm ~= HTermRecord(Id);
    NextHTerm = cast(int) HTerm.length;
    return NextHTerm - 1;
}

int FindHNont(int Id) nothrow @safe
{
    foreach (sym; firstHNont .. cast(int) HNont.length)
        if (HNont[sym].Id == Id)
            return sym;
    HNont.length = NextHNont;
    HNont ~= HNontRecord(Id, Id, -1, null, false);
    NextHNont = cast(int) HNont.length;
    return NextHNont - 1;
}

int NewAnonymNont(int Id) nothrow @safe
{
    HNont.length = NextHNont;
    HNont ~= HNontRecord(NextAnonym, Id, -1, null, false);
    --NextAnonym;
    NextHNont = cast(int) HNont.length;
    return NextHNont - 1;
}

void AppDom(char Dir, int Dom) nothrow @safe
{
    if (Dir == '-')
        Dom = -Dom;
    DomBuf.length = NextDom;
    DomBuf ~= Dom;
    NextDom = cast(int) DomBuf.length;
}

bool WellMatched(int Sig1, int Sig2) @nogc nothrow @safe
{
    if (Sig1 == Sig2)
        return true;
    while (DomBuf[Sig1] == DomBuf[Sig2] && DomBuf[Sig1] != nil && DomBuf[Sig2] != nil)
    {
        ++Sig1;
        ++Sig2;
    }
    return DomBuf[Sig1] == nil && DomBuf[Sig2] == nil;
}

bool SigOK(int Sym) nothrow @safe
{
    if (HNont[Sym].Sig < 0)
    {
        HNont[Sym].Sig = CurSig;
        AppDom('+', nil);
        CurSig = NextDom;
        return true;
    }
    DomBuf.length = NextDom;
    DomBuf ~= nil;
    NextDom = CurSig;
    return WellMatched(HNont[Sym].Sig, CurSig);
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

void NewTerm(ref Factor F, int Sym, Position Pos) nothrow @safe
{
    Term F1 = new Term;

    ++NOTerm;
    F1.Next = null;
    F1.Sym = Sym;
    F1.Pos = Pos;
    F1.Ind = NextHFactor;
    ++NextHFactor;
    if (F is null)
    {
        F = F1;
        F.Prev = null;
    }
    else
    {
        F.Next = F1;
        F1.Prev = F;
        F = F.Next;
    }
}

void NewNont(ref Factor F, int Sym, ParamsDesc Actual, Position Pos) nothrow @safe
{
    Nont F1 = new Nont;

    ++NONont;
    F1.Next = null;
    F1.Sym = Sym;
    F1.Actual = Actual;
    F1.Pos = Pos;
    F1.Ind = NextHFactor;
    ++NextHFactor;
    if (F is null)
    {
        F = F1;
        F.Prev = null;
    }
    else
    {
        F.Next = F1;
        F1.Prev = F;
        F = F.Next;
    }
}

void NewGrp(int Sym, Alt Sub) nothrow @safe
{
    if (HNont[Sym].Def is null)
    {
        Grp N = new Grp;

        ++NOGrp;
        N.Sub = Sub;
        HNont[Sym].Def = N;
    }
    else
    {
        Alt A = (cast(Grp) HNont[Sym].Def).Sub;

        while (A.Next !is null)
            A = A.Next;
        A.Next = Sub;
    }
}

void NewOpt(int Sym, Alt Sub, ParamsDesc Formal, Position Pos) nothrow @safe
{
    Opt N = new Opt;

    ++NOOpt;
    N.Sub = Sub;
    N.EmptyAltPos = Pos;
    N.Scope.Beg = nil;
    N.Scope.End = nil;
    N.Formal = Formal;
    HNont[Sym].Def = N;
}

void NewRep(int Sym, Alt Sub, ParamsDesc Formal, Position Pos) nothrow @safe
{
    Rep N = new Rep;

    ++NORep;
    N.Sub = Sub;
    N.EmptyAltPos = Pos;
    N.Scope.Beg = nil;
    N.Scope.End = nil;
    N.Formal = Formal;
    HNont[Sym].Def = N;
}

void NewAlt(ref Alt A, int Sym, ParamsDesc Formal, ParamsDesc Actual, Factor Sub,
        Factor Last, Position Pos) nothrow @safe
{
    Alt A1 = new Alt;

    ++NOAlt;
    A1.Next = null;
    A1.Up = Sym;
    A1.Scope.Beg = nil;
    A1.Scope.End = nil;
    A1.Formal = Formal;
    A1.Actual = Actual;
    A1.Sub = Sub;
    A1.Last = Last;
    A1.Pos = Pos;
    A1.Ind = NextHAlt;
    ++NextHAlt;
    if (A is null)
    {
        A = A1;
    }
    else
    {
        A.Next = A1;
        A = A.Next;
    }
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

void Init() nothrow
{
    ParamBuf = null;
    AppParam(nil, UndefPos);

    MTerm = null;
    MTerm ~= MTermRecord.init;
    NextMTerm = cast(int) MTerm.length;

    MNont = null;
    MNont ~= MNontRecord.init;
    NextMNont = cast(int) MNont.length;

    HTerm = null;
    NextHTerm = cast(int) HTerm.length;

    HNont = null;
    NextHNont = cast(int) HNont.length;
    NextAnonym = -1;

    DomBuf = null;
    AppDom('+', nil);
    CurSig = NextDom;

    MAlt = null;
    MAlt ~= MAltRecord.init;
    NextMAlt = cast(int) MAlt.length;

    MembBuf = null;
    MembBuf ~= 0;
    NextMemb = cast(int) MembBuf.length;

    NodeBuf = null;
    NodeBuf ~= 0;
    NextNode = cast(int) NodeBuf.length;

    Var = null;
    Var ~= VarRecord.init;
    NextVar = cast(int) Var.length;
    Scope = NextVar;

    NextHAlt = firstHAlt;
    NextHFactor = firstHFactor;
    Null.length = 0;
    Prod.length = 0;
    Pred.length = 0;
    NOAlt = 0;
    NOTerm = 0;
    NONont = 0;
    NOGrp = 0;
    NOOpt = 0;
    NORep = 0;
    BaseName = "nothing";
    MaxMArity = 0;

    symbolTable = new SymbolTable;
}
}

// Transitional legacy instance. Generator entry points will receive EAG explicitly.
EAG eag;

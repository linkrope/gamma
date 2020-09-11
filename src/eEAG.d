module eEAG;

import runtime;
import Sets = eSets;
import IO = eIO;
import Scanner = eScanner;
import io : Position;

const nil = 0;
const empty = 0;
const analysed = 0;
const predicates = 1;
const parsable = 2;
const isSLEAG = 3;
const isSSweep = 4;
const hasEvaluator = 5;
uint History;
const firstParam = 0;
const firstHAlt = 0;
const firstHFactor = 0;

struct ParamsDesc
{
    int Params;
    Position Pos;

    public string toString() const
    {
        import std.format : format;

        return format!"ParamsDesc(Params=%s)"(Params);
    }
}

struct ParamRecord
{
    int Affixform;
    Position Pos;
    bool isDef;

    public string toString() const
    {
        import std.format : format;

        if (Affixform == nil)
            return "Param()";
        return format!"Param(%s %s)"(isDef ? "def" : "app", Affixform);
    }
}

alias OpenParamBuf = ParamRecord[];
OpenParamBuf ParamBuf;
int NextParam;
const firstNode = 1;
const firstVar = 1;

struct ScopeDesc
{
    int Beg;
    int End;

    public string toString() const
    {
        import std.format : format;

        return format!"Scope(Beg=%s, End=%s)"(Beg, End);
    }
}

alias OpenNodeBuf = int[];

struct VarRecord
{
    int Sym;
    int Num;
    int Neg;
    Position Pos;
    bool Def;
}

alias OpenVar = VarRecord[];
OpenNodeBuf NodeBuf;
int NextNode;
OpenVar Var;
int NextVar;
int Scope;
alias Rule = RuleDesc;
alias Alt = AltDesc;

class RuleDesc
{
    Alt Sub;
}

alias Factor = FactorDesc;

class AltDesc
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

    public override string toString() const
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

void assign(AltDesc lhs, AltDesc rhs)
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

class Grp : RuleDesc
{
}

class Opt : RuleDesc
{
    Position EmptyAltPos;
    ScopeDesc Scope;
    ParamsDesc Formal;
}

class Rep : RuleDesc
{
    Position EmptyAltPos;
    ScopeDesc Scope;
    ParamsDesc Formal;
}

class FactorDesc
{
    int Ind;
    Factor Prev;
    Factor Next;
}

class Term : FactorDesc
{
    int Sym;
    Position Pos;
}

class Nont : FactorDesc
{
    int Sym;
    ParamsDesc Actual;
    Position Pos;

}

void assign(Nont lhs, Nont rhs)
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

int NextHAlt;
int NextHFactor;
int NOAlt;
int NOTerm;
int NONont;
int NOOpt;
int NORep;
int NOGrp;
const firstDom = 0;
alias OpenDomBuf = int[];
OpenDomBuf DomBuf;
int NextDom;
int CurSig;
const firstMAlt = 1;
const firstMemb = 1;

struct MAltRecord
{
    int Left;
    int Right;
    int Arity;
    int Next;
}

alias OpenMAlt = MAltRecord[];
alias OpenMembBuf = int[];
OpenMAlt MAlt;
int NextMAlt;
int MaxMArity;
OpenMembBuf MembBuf;
int NextMemb;
const firstMTerm = 1;
const firstMNont = 1;
const firstHTerm = 0;
const firstHNont = 0;

struct MTermRecord
{
    int Id;
}

alias OpenMTerm = MTermRecord[];

struct MNontRecord
{
    int Id;
    int MRule;
    int Last;
    bool IsToken;
}

alias OpenMNont = MNontRecord[];

struct HTermRecord
{
    int Id;
}

alias OpenHTerm = HTermRecord[];

struct HNontRecord
{
    int Id;
    int NamedId;
    int Sig;
    RuleDesc Def;
    bool IsToken;
}

alias OpenHNont = HNontRecord[];
OpenMTerm MTerm;
int NextMTerm;
OpenMNont MNont;
int NextMNont;
OpenHTerm HTerm;
int NextHTerm;
OpenHNont HNont;
int NextHNont;
int NextAnonym;
const BaseNameLen = 18;
Sets.OpenSet All;
Sets.OpenSet Prod;
Sets.OpenSet Reach;
Sets.OpenSet Null;
Sets.OpenSet Pred;
int StartSym;
char[BaseNameLen] BaseName;

void Expand()
{
    long i;

    long NewLen(long ArrayLen)
    {
        if (ArrayLen < DIV(int.max, 2))
        {
            return 2 * ArrayLen + 1;
        }
        else
        {
            assert(0);
        }
    }

    if (NextParam >= ParamBuf.length)
    {
        OpenParamBuf ParamBuf1 = new ParamRecord[NewLen(ParamBuf.length)];

        for (i = firstParam; i <= ParamBuf.length - 1; ++i)
        {
            ParamBuf1[i] = ParamBuf[i];
        }
        ParamBuf = ParamBuf1;
    }
    if (NextMTerm >= MTerm.length)
    {
        OpenMTerm MTerm1 = new MTermRecord[NewLen(MTerm.length)];

        for (i = firstMTerm; i <= MTerm.length - 1; ++i)
        {
            MTerm1[i] = MTerm[i];
        }
        MTerm = MTerm1;
    }
    if (NextMNont >= MNont.length)
    {
        OpenMNont MNont1 = new MNontRecord[NewLen(MNont.length)];

        for (i = firstMNont; i <= MNont.length - 1; ++i)
        {
            MNont1[i] = MNont[i];
        }
        MNont = MNont1;
    }
    if (NextHTerm >= HTerm.length)
    {
        OpenHTerm HTerm1 = new HTermRecord[NewLen(HTerm.length)];

        for (i = firstHTerm; i <= HTerm.length - 1; ++i)
        {
            HTerm1[i] = HTerm[i];
        }
        HTerm = HTerm1;
    }
    if (NextHNont >= HNont.length)
    {
        OpenHNont HNont1 = new HNontRecord[NewLen(HNont.length)];

        for (i = firstHNont; i <= HNont.length - 1; ++i)
        {
            HNont1[i] = HNont[i];
        }
        HNont = HNont1;
    }
    if (NextDom >= DomBuf.length)
    {
        OpenDomBuf DomBuf1 = new int[NewLen(DomBuf.length)];

        for (i = firstDom; i <= DomBuf.length - 1; ++i)
        {
            DomBuf1[i] = DomBuf[i];
        }
        DomBuf = DomBuf1;
    }
    if (NextMAlt >= MAlt.length)
    {
        OpenMAlt MAlt1 = new MAltRecord[NewLen(MAlt.length)];

        for (i = firstMAlt; i <= MAlt.length - 1; ++i)
        {
            MAlt1[i] = MAlt[i];
        }
        MAlt = MAlt1;
    }
    if (NextMemb >= MembBuf.length)
    {
        OpenMembBuf MembBuf1 = new int[NewLen(MembBuf.length)];

        for (i = firstMemb; i <= MembBuf.length - 1; ++i)
        {
            MembBuf1[i] = MembBuf[i];
        }
        MembBuf = MembBuf1;
    }
    if (NextNode >= NodeBuf.length)
    {
        OpenNodeBuf NodeBuf1 = new int[NewLen(NodeBuf.length)];

        for (i = firstNode; i <= NodeBuf.length - 1; ++i)
        {
            NodeBuf1[i] = NodeBuf[i];
        }
        NodeBuf = NodeBuf1;
    }
    if (NextVar >= Var.length)
    {
        OpenVar Var1 = new VarRecord[NewLen(Var.length)];

        for (i = firstVar; i <= Var.length - 1; ++i)
        {
            Var1[i] = Var[i];
        }
        Var = Var1;
    }
}

void AppParam(int Affixform, Position Pos)
{
    ParamBuf[NextParam].Affixform = Affixform;
    ParamBuf[NextParam].Pos = Pos;
    ++NextParam;
    if (NextParam >= ParamBuf.length)
    {
        Expand;
    }
}

int FindMTerm(int Id)
{
    int Sym;
    Sym = firstMTerm;
    MTerm[NextMTerm].Id = Id;
    while (Id != MTerm[Sym].Id)
    {
        ++Sym;
    }
    if (Sym == NextMTerm)
    {
        ++NextMTerm;
        if (NextMTerm >= MTerm.length)
        {
            Expand;
        }
    }
    return Sym;
}

int FindMNont(int Id)
{
    int Sym;
    Sym = firstMNont;
    MNont[NextMNont].Id = Id;
    while (Id != MNont[Sym].Id)
    {
        ++Sym;
    }
    if (Sym == NextMNont)
    {
        MNont[NextMNont].MRule = nil;
        MNont[NextMNont].Last = nil;
        MNont[NextMNont].IsToken = false;
        ++NextMNont;
        if (NextMNont >= MNont.length)
        {
            Expand;
        }
    }
    return Sym;
}

int FindHTerm(int Id)
{
    int Sym;
    Sym = firstHTerm;
    HTerm[NextHTerm].Id = Id;
    while (Id != HTerm[Sym].Id)
    {
        ++Sym;
    }
    if (Sym == NextHTerm)
    {
        ++NextHTerm;
        if (NextHTerm >= HTerm.length)
        {
            Expand;
        }
    }
    return Sym;
}

int FindHNont(int Id)
{
    int Sym;
    Sym = firstHNont;
    HNont[NextHNont].Id = Id;
    while (Id != HNont[Sym].Id)
    {
        ++Sym;
    }
    if (Sym == NextHNont)
    {
        HNont[NextHNont].NamedId = Id;
        HNont[NextHNont].Sig = -1;
        HNont[NextHNont].Def = null;
        HNont[NextHNont].IsToken = false;
        ++NextHNont;
        if (NextHNont >= HNont.length)
        {
            Expand;
        }
    }
    return Sym;
}

int NewAnonymNont(int Id)
{
    HNont[NextHNont].Id = NextAnonym;
    HNont[NextHNont].NamedId = Id;
    HNont[NextHNont].Sig = -1;
    HNont[NextHNont].Def = null;
    HNont[NextHNont].IsToken = false;
    --NextAnonym;
    ++NextHNont;
    if (NextHNont >= HNont.length)
    {
        Expand;
    }
    return NextHNont - 1;
}

void AppDom(char Dir, int Dom)
{
    if (Dir == '-')
    {
        Dom = -Dom;
    }
    DomBuf[NextDom] = Dom;
    ++NextDom;
    if (NextDom >= DomBuf.length)
    {
        Expand;
    }
}

bool WellMatched(int Sig1, int Sig2)
{
    if (Sig1 == Sig2)
    {
        return true;
    }
    else
    {
        while (DomBuf[Sig1] == DomBuf[Sig2] && DomBuf[Sig1] != nil && DomBuf[Sig2] != nil)
        {
            ++Sig1;
            ++Sig2;
        }
        return DomBuf[Sig1] == nil && DomBuf[Sig2] == nil;
    }
}

bool SigOK(int Sym)
{
    if (HNont[Sym].Sig < 0)
    {
        HNont[Sym].Sig = CurSig;
        DomBuf[NextDom] = nil;
        ++NextDom;
        if (NextDom >= DomBuf.length)
        {
            Expand;
        }
        CurSig = NextDom;
        return true;
    }
    else
    {
        DomBuf[NextDom] = nil;
        NextDom = CurSig;
        return WellMatched(HNont[Sym].Sig, CurSig);
    }
}

int NewMAlt(int Sym, int Right)
{
    int Arity;
    int i;
    MAlt[NextMAlt].Next = nil;
    if (MNont[Sym].MRule == nil)
    {
        MNont[Sym].MRule = NextMAlt;
    }
    else
    {
        MAlt[MNont[Sym].Last].Next = NextMAlt;
    }
    MNont[Sym].Last = NextMAlt;
    MAlt[NextMAlt].Left = Sym;
    MAlt[NextMAlt].Right = Right;
    i = Right;
    Arity = 0;
    while (MembBuf[i] != 0)
    {
        if (MembBuf[i] > 0)
        {
            ++Arity;
        }
        ++i;
    }
    MAlt[NextMAlt].Arity = Arity;
    if (Arity > MaxMArity)
    {
        MaxMArity = Arity;
    }
    ++NextMAlt;
    if (NextMAlt >= MAlt.length)
    {
        Expand;
    }
    return NextMAlt - 1;
}

void AppMemb(int Val)
{
    MembBuf[NextMemb] = Val;
    ++NextMemb;
    if (NextMemb >= MembBuf.length)
    {
        Expand;
    }
}

int FindVar(int Sym, int Num, Position Pos, bool Def)
{
    int V;
    V = Scope;
    Var[NextVar].Sym = Sym;
    Var[NextVar].Num = Num;
    while (Var[V].Sym != Sym || Var[V].Num != Num)
    {
        ++V;
    }
    if (V == NextVar)
    {
        V = Scope;
        Var[NextVar].Num = -Num;
        while (Var[V].Sym != Sym || Var[V].Num != -Num)
        {
            ++V;
        }
        if (V != NextVar)
        {
            Var[V].Neg = NextVar;
            Var[NextVar].Neg = V;
        }
        else
        {
            Var[NextVar].Neg = nil;
        }
        V = NextVar;
        Var[NextVar].Num = Num;
        Var[NextVar].Pos = Pos;
        Var[NextVar].Def = Def;
        ++NextVar;
        if (NextVar >= Var.length)
        {
            Expand;
        }
    }
    else
    {
        Var[V].Def = Var[V].Def || Def;
    }
    return V;
}

void NewTerm(ref Factor F, int Sym, Position Pos)
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

void NewNont(ref Factor F, int Sym, ParamsDesc Actual, Position Pos)
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

void NewGrp(int Sym, Alt Sub)
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
        {
            A = A.Next;
        }
        A.Next = Sub;
    }
}

void NewOpt(int Sym, Alt Sub, ParamsDesc Formal, Position Pos)
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

void NewRep(int Sym, Alt Sub, ParamsDesc Formal, Position Pos)
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
        Factor Last, Position Pos)
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

void WriteHTerm(ref IO.TextOut Out, int Term)
{
    Scanner.WriteRepr(Out, HTerm[Term].Id);
}

public string HNontToString(int Nont)
{
    import std.format : format;

    if (HNont[Nont].Id < 0)
        return format!"A%s"(-HNont[Nont].Id);
    return Scanner.toString(HNont[Nont].Id);
}

void WriteHNont(ref IO.TextOut Out, int Nont)
{
    if (HNont[Nont].Id < 0)
    {
        IO.Write(Out, 'A');
        IO.WriteInt(Out, -HNont[Nont].Id);
    }
    else
    {
        Scanner.WriteRepr(Out, HNont[Nont].Id);
    }
}

void WriteVar(ref IO.TextOut Out, int V)
{
    import std.math : abs;

    if (Var[V].Num < 0)
    {
        IO.Write(Out, '#');
    }
    Scanner.WriteRepr(Out, MNont[Var[V].Sym].Id);
    if (abs(Var[V].Num) > 1)
    {
        IO.WriteInt(Out, abs(Var[V].Num) - 2);
    }
}

void WriteNamedHNont(ref IO.TextOut Out, int Nont)
{
    Scanner.WriteRepr(Out, HNont[Nont].NamedId);
}

bool Performed(uint Needed)
{
    Needed = Needed & ~History;
    if (Needed == Sets.SET)
    {
        return true;
    }
    else
    {
        if (Sets.IN(Needed, analysed))
        {
            IO.WriteText(IO.Msg, "\n\tanalyse a specification first");
        }
        if (Sets.IN(Needed, predicates))
        {
            IO.WriteText(IO.Msg, "\n\tcheck for predicates first");
        }
        if (Sets.IN(Needed, parsable))
        {
            IO.WriteText(IO.Msg, "\n\ttest for ELL1 attribute first");
        }
        if (Sets.IN(Needed, isSLEAG))
        {
            IO.WriteText(IO.Msg, "\n\ttest for SLEAG attribute first");
        }
        if (Sets.IN(Needed, isSSweep))
        {
            IO.WriteText(IO.Msg, "\n\ttest for single sweep attribute first");
        }
        if (Sets.IN(Needed, hasEvaluator))
        {
            IO.WriteText(IO.Msg, "\n\tgenerate an evaluator first");
        }
        IO.Update(IO.Msg);
        return false;
    }
}

void Init()
{
    ParamBuf = new ParamRecord[1023];
    NextParam = firstParam;
    ParamBuf[NextParam].Affixform = nil;
    ++NextParam;

    MTerm = new MTermRecord[255];
    NextMTerm = firstMTerm;

    MNont = new MNontRecord[255];
    NextMNont = firstMNont;

    HTerm = new HTermRecord[255];
    NextHTerm = firstHTerm;

    HNont = new HNontRecord[255];
    NextHNont = firstHNont;
    NextAnonym = -1;

    DomBuf = new int[255];
    NextDom = firstDom;
    DomBuf[NextDom] = nil;
    ++NextDom;
    CurSig = NextDom;

    MAlt = new MAltRecord[255];
    NextMAlt = firstMAlt;

    MembBuf = new int[255];
    NextMemb = firstMemb;

    NodeBuf = new int[1023];
    NextNode = firstNode;

    Var = new VarRecord[511];
    NextVar = firstVar;
    Scope = NextVar;

    NextHAlt = firstHAlt;
    NextHFactor = firstHFactor;
    Null = null;
    Prod = null;
    Pred = null;
    NOAlt = 0;
    NOTerm = 0;
    NONont = 0;
    NOGrp = 0;
    NOOpt = 0;
    NORep = 0;
    History = Sets.SET;
    BaseName = "nothing";
    MaxMArity = 0;
}

static this()
{
    History = Sets.SET;
    BaseName = "nothing";
    IO.WriteText(IO.Msg, "Epsilon 1.02   JoDe/SteWe  22.11.96\n");
    IO.Update(IO.Msg);
}

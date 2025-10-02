module epsilon.ell1gen;

import core.time : MonoTime;
import EAG = epsilon.eag;
import EmitGen = epsilon.emitgen;
import epsilon.settings;
import Shift = epsilon.shift;
import EvalGen = epsilon.slaggen;
import io : Input, Position, read;
import log;
import runtime;
import std.bitmanip : BitArray;
import std.conv : to;
import std.format;
import std.typecons;

private const nil = 0;
private const endTok = 0;
private const undefTok = 1;
private const sepTok = 2;
private const firstUserTok = 3;
private enum nElemsPerSET = size_t.sizeof * 8;
private const firstEdge = 1;
private const firstGenSet = 1;
private const firstGenSetT = 1;

private struct NontRecord
{
    BitArray First;
    BitArray Follow;
    BitArray IniFollow;
    EAG.Alt DefaultAlt;
    int Edge;
    int AltRec;
    int OptRec;
    int AltExp;
    int OptExp;
    int FirstIndex;
    int FollowIndex;
    bool Anonym;
}

private struct AltRecord
{
    BitArray Dir;
}

private struct FactorRecord
{
    int Rec;
}

private struct EdgeRecord
{
    int Dest;
    int Next;
}

private NontRecord[] Nont;
private AltRecord[] Alt;
private FactorRecord[] Factor;
private EdgeRecord[] Edge;
private int NextEdge;
private BitArray[] GenSet;
private int NextGenSet;
private BitArray[] GenSetT;
private int NextGenSetT;
private BitArray TestNonts;
private BitArray GenNonts;
private BitArray RegNonts;
private BitArray ConflictNonts;
private int nToks;
public bool Error;
private bool Warning;
private bool UseReg;

public void Test(Settings settings)
in (EAG.Performed(EAG.analysed | EAG.predicates))
{
    info!"ELL(1) testing %s"(EAG.BaseName);
    EAG.History &= ~EAG.parsable;
    Init(settings);
    scope (exit)
        Finit;
    if (!GrammarOk)
        return;
    ComputeDir;
    if (Error || Warning)
        return;
    info!"%s grammar is ELL(1)"(EAG.BaseName);
    EAG.History |= EAG.parsable;
}

public string Generate(Settings settings)
in (EAG.Performed(EAG.analysed | EAG.predicates | EAG.isSLAG))
{
    info!"ELL(1) writing %s"(EAG.BaseName);
    EAG.History &= ~EAG.parsable;
    Init(settings);
    scope (exit)
        Finit;
    if (!GrammarOk)
        assert(0, "TODO: error handling for parser generator");
    ComputeDir;
    if (Error)
        assert(0, "TODO: error handling for parser generator");
    ComputeDefaultAlts;
    ComputeSets;

    const fileName = GenerateMod(No.parsePass, settings);

    EAG.History |= EAG.parsable;
    return fileName;
}

public string GenerateParser(Settings settings)
in (EAG.Performed(EAG.analysed | EAG.predicates | EAG.hasEvaluator))
{
    info!"ELL(1) writing parser of %s"(EAG.BaseName);
    EAG.History &= ~EAG.parsable;
    Init(settings);
    scope (exit)
        Finit;
    if (!GrammarOk)
        assert(0, "TODO: error handling for parser generator");
    EAG.History = 0;
    Shift.Shift;
    ComputeDir;
    if (Error)
        assert(0, "TODO: error handling for parser generator");
    ComputeDefaultAlts;
    ComputeSets;
    return GenerateMod(Yes.parsePass, settings);
}

private void Init(Settings settings)
{
    int i;

    nToks = EAG.NextHTerm - EAG.firstHTerm + firstUserTok;
    if (EAG.NextHNont >= 1)
        Nont = new NontRecord[EAG.NextHNont];
    else
        Nont = new NontRecord[1];
    for (i = EAG.firstHNont; i < EAG.NextHNont; ++i)
    {
        Nont[i].First = BitArray();
        Nont[i].First.length = nToks + 1;
        Nont[i].Follow = BitArray();
        Nont[i].Follow.length = nToks + 1;
        Nont[i].IniFollow = BitArray();
        Nont[i].IniFollow.length = nToks + 1;

        Nont[i].DefaultAlt = null;
        Nont[i].AltRec = nil;
        Nont[i].OptRec = nil;
        Nont[i].AltExp = nil;
        Nont[i].OptExp = nil;
        Nont[i].FirstIndex = nil;
        Nont[i].FollowIndex = nil;
        Nont[i].Anonym = EAG.All[i] && EAG.HNont[i].anonymous;
    }
    if (EAG.NextHAlt >= 1)
        Alt = new AltRecord[EAG.NextHAlt];
    else
        Alt = new AltRecord[1];
    for (i = EAG.firstHAlt; i < EAG.NextHAlt; ++i)
    {
        Alt[i].Dir = BitArray();
        Alt[i].Dir.length = nToks + 1;
    }
    if (EAG.NextHFactor >= 1)
        Factor = new FactorRecord[EAG.NextHFactor];
    else
        Factor = new FactorRecord[1];
    for (i = EAG.firstHFactor; i < EAG.NextHFactor; ++i)
        Factor[i].Rec = nil;
    Edge = new EdgeRecord[255];
    NextEdge = firstEdge;
    GenSet = new BitArray[511];
    NextGenSet = firstGenSet;
    GenSetT = new BitArray[255];
    NextGenSetT = firstGenSetT;
    TestNonts = EAG.All - EAG.Pred;
    GenNonts = EAG.Prod & EAG.Reach;
    GenNonts -= EAG.Pred;
    Error = false;
    Warning = false;
    UseReg = !settings.p;
    RegNonts = BitArray();
    RegNonts.length = EAG.NextHNont + 1;
    ConflictNonts = BitArray();
    ConflictNonts.length = EAG.NextHNont + 1;
    if (UseReg)
        ComputeRegNonts;
}

/**
 * R  whole procedure
 */
private void ComputeRegNonts()
{
    EAG.Alt A;
    EAG.Factor F;

    void TraverseRegNonts(size_t N)
    {
        EAG.Alt A = EAG.HNont[N].Def.Sub;

        do
        {
            EAG.Factor F = A.Sub;

            while (F !is null)
            {
                if (auto nont = cast(EAG.Nont) F)
                    if (TestNonts[nont.Sym] && !RegNonts[nont.Sym])
                    {
                        RegNonts[nont.Sym] = true;
                        TraverseRegNonts(nont.Sym);
                    }
                F = F.Next;
            }
            A = A.Next;
        }
        while (A !is null);
    }

    void DeleteConflictNont(int N)
    {
        EAG.Alt A = EAG.HNont[N].Def.Sub;

        ConflictNonts[N] = false;
        do
        {
            for (EAG.Factor F = A.Sub; F !is null; F = F.Next)
                if (auto nont = cast(EAG.Nont) F)
                    if (ConflictNonts[nont.Sym])
                        DeleteConflictNont(nont.Sym);
            A = A.Next;
        }
        while (A !is null);
    }

    RegNonts[] = false;
    foreach (N; TestNonts.bitsSet)
    if (TestNonts[N] && EAG.HNont[N].IsToken && !RegNonts[N])
    {
        RegNonts[N] = true;
        TraverseRegNonts(N);
    }
    ConflictNonts = RegNonts.dup;
    foreach (N; ConflictNonts.bitsSet)
    if (ConflictNonts[N])
    {
        A = EAG.HNont[N].Def.Sub;
        do
        {
            F = A.Last;
            while (F !is null && cast(EAG.Nont) F && !TestNonts[(cast(EAG.Nont) F).Sym])
                F = F.Prev;
            if (F !is null)
                F = F.Prev;
            while (F !is null)
            {
                if (auto nont = cast(EAG.Nont) F)
                    if (ConflictNonts[nont.Sym])
                        DeleteConflictNont(nont.Sym);
                F = F.Prev;
            }
            A = A.Next;
        }
        while (A !is null);
    }
}

private void Finit() @nogc nothrow @safe
{
    Nont = null;
    Alt = null;
    Factor = null;
    Edge = null;
    GenSet = null;
    GenSetT = null;
}

/**
 * R  whole procedure
 */
private bool GrammarOk()
{
    EAG.Alt A;
    EAG.Factor F;
    bool Ok = true;

    if (UseReg)
    {
        if (RegNonts[EAG.StartSym])
        {
            if (EAG.HNont[EAG.StartSym].IsToken)
                error!"start symbol must not be a token";
            else
                error!"start symbol must not be a sub-token";
            Ok = false;
        }
        foreach (N; TestNonts.bitsSet)
            if (EAG.HNont[N].IsToken)
            {
                if (EAG.Null[N])
                {
                    error!"marked token %s is nullable"(EAG.HNontRepr(N));
                    Ok = false;
                }
                if (Nont[N].Anonym)
                {
                    fatal!"token in %s is anonymous"(EAG.NamedHNontRepr(N));
                    Ok = false;
                }
            }
        foreach (N; TestNonts.bitsSet)
            if (!RegNonts[N])
            {
                A = EAG.HNont[N].Def.Sub;
                do
                {
                    F = A.Sub;
                    while (F !is null)
                    {
                        if (auto nont = cast(EAG.Nont) F)
                            if (TestNonts[nont.Sym] && RegNonts[nont.Sym] && !EAG.HNont[nont.Sym].IsToken)
                            {
                                if (Nont[N].Anonym)
                                    error!"nonterminal in %s calls sub-token %s"(
                                            EAG.NamedHNontRepr(N), EAG.HNontRepr(nont.Sym));
                                else
                                    error!"nonterminal %s calls sub-token %s"(
                                            EAG.HNontRepr(N), EAG.HNontRepr(nont.Sym));
                                Ok = false;
                            }
                        F = F.Next;
                    }
                    A = A.Next;
                }
                while (A !is null);
            }
    }
    return Ok;
}

private void ComputeDir()
{
    EAG.Alt A;
    EAG.Factor F;
    int[] State;
    size_t[] Stack;
    int Top;
    BitArray NullAlts;
    BitArray Toks;
    bool IsLast;

    void ComputeFirst(size_t N)
    {
        int n;
        int E;
        size_t N1;
        bool leftRecursion = false;

        Stack[Top] = N;
        ++Top;
        n = Top;
        State[N] = n;
        E = Nont[N].Edge;
        while (E != nil)
        {
            N1 = Edge[E].Dest;
            if (N1 == N)
                leftRecursion = true;
            if (State[N1] == 0)
                ComputeFirst(N1);
            if (State[N1] < State[N])
                State[N] = State[N1];
            Nont[N].First |= Nont[N1].First;
            E = Edge[E].Next;
        }
        if (State[N] == n)
        {
            string[] items;

            leftRecursion = leftRecursion || Top > n;
            do
            {
                --Top;
                N1 = Stack[Top];
                State[N1] = int.max;
                if (leftRecursion)
                {
                    if (Nont[N1].Anonym)
                    {
                        items ~= format!"EBNF expression in %s\n%s"
                            (EAG.NamedHNontRepr(N1), EAG.HNont[N1].Def.Sub.Pos);
                    }
                    else
                    {
                        items ~= EAG.NamedHNontRepr(N1);
                    }
                }
                Nont[N1].First = Nont[N].First;
            }
            while (Top >= n);
            if (leftRecursion)
            {
                error!"left recursion over nonterminals%-(\n%s%)"(items);
                Error = true;
            }
        }
    }

    void ComputeFollow(size_t N)
    {
        int n;
        int E;
        size_t N1;

        Stack[Top] = N;
        ++Top;
        n = Top;
        State[N] = n;
        E = Nont[N].Edge;
        while (E != nil)
        {
            N1 = Edge[E].Dest;
            if (State[N1] == 0)
                ComputeFollow(N1);
            if (State[N1] < State[N])
                State[N] = State[N1];
            Nont[N].Follow |= Nont[N1].Follow;
            E = Edge[E].Next;
        }
        if (State[N] == n)
        {
            do
            {
                --Top;
                N1 = Stack[Top];
                State[N1] = int.max;
                Nont[N1].Follow = Nont[N].Follow;
            }
            while (Top >= n);
        }
    }

    void Conflict(size_t N, Position Pos, BitArray Dir, BitArray PrevDirs)
    {
        import std.algorithm : map;

        const msg = format!"director set conflict in %s: %-(%s, %)\n%s"
            (EAG.NamedHNontRepr(N), (Dir & PrevDirs).bitsSet.map!TokRepr, Pos);

        if ((Dir - PrevDirs).bitsSet.empty)
        {
            error!"%s\nalternative will never be chosen"(msg);
            Error = true;
        }
        else
        {
            warn!"%s"(msg);
            Warning = true;
        }
    }

    State = new int[EAG.NextHNont];
    Stack = new size_t[EAG.NextHNont];
    Top = 0;
    NullAlts = BitArray();
    NullAlts.length = EAG.NextHAlt;
    Toks = BitArray();
    Toks.length = nToks + 1;
    NextEdge = firstEdge;
    for (size_t N = EAG.firstHNont; N < EAG.NextHNont; ++N)
    {
        Nont[N].Edge = nil;
        State[N] = 0;
    }
    foreach (N; TestNonts.bitsSet)
    {
        Nont[N].First[] = false;
        A = EAG.HNont[N].Def.Sub;
        do
        {
            F = A.Sub;
            for (;;)
            {
                if (F is null)
                    break;
                if (auto term = cast(EAG.Term) F)
                {
                    Nont[N].First[term.Sym - EAG.firstHTerm + firstUserTok] = true;
                    break;
                }
                else if (auto nont = cast(EAG.Nont) F)
                {
                    if (TestNonts[nont.Sym])
                    {
                        NewEdge(N, nont.Sym);
                        if (!EAG.Null[nont.Sym])
                            break;
                    }
                }
                F = F.Next;
            }
            A = A.Next;
        }
        while (A !is null);
    }
    foreach (N; TestNonts.bitsSet)
        if (State[N] == 0)
            ComputeFirst(N);
    NextEdge = firstEdge;
    for (size_t N = EAG.firstHNont; N < EAG.NextHNont; ++N)
    {
        Nont[N].Edge = nil;
        Nont[N].Follow[] = false;
    }
    Nont[EAG.StartSym].Follow[endTok] = true;
    NullAlts[] = false;
    foreach (N; TestNonts.bitsSet)
    {
        A = EAG.HNont[N].Def.Sub;
        do
        {
            if (cast(EAG.Rep) EAG.HNont[N].Def !is null)
                Toks = Nont[N].First.dup;
            else
                Toks[] = false;
            F = A.Last;
            IsLast = true;
            while (F !is null)
            {
                if (auto term = cast(EAG.Term) F)
                {
                    Toks[] = false;
                    Toks[term.Sym - EAG.firstHTerm + firstUserTok] = true;
                    IsLast = false;
                }
                else if (auto nont = cast(EAG.Nont) F)
                {
                    if (TestNonts[nont.Sym])
                    {
                        if (IsLast)
                            NewEdge(nont.Sym, N.to!int);
                        Nont[nont.Sym].Follow |= Toks;
                        if (UseReg && !RegNonts[N] && RegNonts[nont.Sym])
                            Nont[nont.Sym].Follow[sepTok] = true;
                        if (EAG.Null[nont.Sym])
                        {
                            Toks |= Nont[nont.Sym].First;
                        }
                        else
                        {
                            Toks = Nont[nont.Sym].First.dup;
                            IsLast = false;
                        }
                    }
                }
                F = F.Prev;
            }
            if (IsLast)
                NullAlts[A.Ind] = true;
            A = A.Next;
        }
        while (A !is null);
    }
    foreach (N; TestNonts.bitsSet)
        Nont[N].IniFollow = Nont[N].Follow.dup;
    for (size_t N = EAG.firstHNont; N < EAG.NextHNont; ++N)
        State[N] = 0;
    foreach (N; TestNonts.bitsSet)
        if (State[N] == 0)
            ComputeFollow(N);
    foreach (N; TestNonts.bitsSet)
    {
        Toks[] = false;
        A = EAG.HNont[N].Def.Sub;
        do
        {
            if (NullAlts[A.Ind])
                Alt[A.Ind].Dir = Nont[N].Follow.dup;
            else
                Alt[A.Ind].Dir[] = false;
            F = A.Sub;
            for (;;)
            {
                if (F is null)
                    break;
                if (auto term = cast(EAG.Term) F)
                {
                    Alt[A.Ind].Dir[term.Sym - EAG.firstHTerm + firstUserTok] = true;
                    break;
                }
                else if (auto nont = cast(EAG.Nont) F)
                {
                    if (TestNonts[nont.Sym])
                    {
                        Alt[A.Ind].Dir |= Nont[nont.Sym].First;
                        if (!EAG.Null[nont.Sym])
                            break;
                    }
                }
                F = F.Next;
            }
            if (!(Alt[A.Ind].Dir & Toks).bitsSet.empty)
            {
                Conflict(N, A.Pos, Alt[A.Ind].Dir, Toks);
                Alt[A.Ind].Dir -= Toks;
            }
            Toks |= Alt[A.Ind].Dir;
            A = A.Next;
        }
        while (A !is null);
        if (cast(EAG.Opt) EAG.HNont[N].Def || cast(EAG.Rep) EAG.HNont[N].Def)
        {
            if (!(Nont[N].Follow & Toks).bitsSet.empty)
            {
                if (!UseReg || !ConflictNonts[N] || Toks[sepTok])
                {
                    if (auto opt = cast(EAG.Opt) EAG.HNont[N].Def)
                        Conflict(N, opt.EmptyAltPos, Nont[N].Follow, Toks);
                    else if (auto rep = cast(EAG.Rep) EAG.HNont[N].Def)
                        Conflict(N, rep.EmptyAltPos, Nont[N].Follow, Toks);
                }
            }
        }
    }
}

private string TokRepr(size_t Tok) @safe
{
    if (Tok == endTok)
        return "<end>";
    else if (Tok == undefTok)
        return "<undef>";
    else if (Tok == sepTok)
        return "<sep>";
    else
        return EAG.HTermRepr(Tok.to!int + EAG.firstHTerm - firstUserTok);
}

private void ComputeDefaultAlts()
{
    struct AltRecord
    {
        int Nont;
        int Deg;
        int Prio;
        EAG.Alt Alt;
    }

    struct StackRecord
    {
        int Nont;
        int APrio;
        EAG.Alt Alt;
    }

    EAG.Alt A;
    EAG.Factor F;
    int E;
    int APrio;
    AltRecord[] Alt;
    StackRecord[] Stack;
    int Top;
    int[] StackPos;
    BitArray DefNonts;

    void TestDeg(int AInd)
    {
        if (Alt[AInd].Deg == 0)
        {
            const N = Alt[AInd].Nont;
            const i = StackPos[N];

            if (i == int.max)
            {
                Stack[Top].Nont = N;
                Stack[Top].APrio = Alt[AInd].Prio;
                Stack[Top].Alt = Alt[AInd].Alt;
                StackPos[N] = Top;
                ++Top;
            }
            else if (i >= 0 && Stack[i].APrio > Alt[AInd].Prio)
            {
                Stack[i].APrio = Alt[AInd].Prio;
                Stack[i].Alt = Alt[AInd].Alt;
            }
        }
    }

    void Pop(ref int Edge)
    {
        int i;
        int MinPrio;
        int MinPos;
        i = Top;
        --Top;
        MinPrio = int.max;
        do
        {
            --i;
            if (Stack[i].APrio < MinPrio)
            {
                MinPrio = Stack[i].APrio;
                MinPos = i;
            }
        }
        while (i != 0 && MinPrio != 1);
        Nont[Stack[MinPos].Nont].DefaultAlt = Stack[MinPos].Alt;
        Edge = Nont[Stack[MinPos].Nont].Edge;
        StackPos[Stack[Top].Nont] = MinPos;
        StackPos[Stack[MinPos].Nont] = -1;
        Stack[MinPos] = Stack[Top];
    }

    if (EAG.NextHAlt >= 1)
        Alt = new AltRecord[EAG.NextHAlt];
    if (EAG.NextHNont >= 1)
        Stack = new StackRecord[EAG.NextHNont];
    Top = 0;
    if (EAG.NextHNont >= 1)
        StackPos = new int[EAG.NextHNont];
    DefNonts = GenNonts.dup;
    NextEdge = firstEdge;
    for (size_t N = EAG.firstHNont; N < EAG.NextHNont; ++N)
    {
        Nont[N].Edge = nil;
        Nont[N].DefaultAlt = null;
        StackPos[N] = int.max;
        if (GenNonts[N] && (cast(EAG.Opt) EAG.HNont[N].Def || cast(EAG.Rep) EAG.HNont[N].Def))
            DefNonts[N] = false;
    }
    foreach (N; DefNonts.bitsSet)
    {
        A = EAG.HNont[N].Def.Sub;
        APrio = 1;
        do
        {
            Alt[A.Ind].Nont = N.to!int;
            Alt[A.Ind].Alt = A;
            Alt[A.Ind].Deg = 0;
            Alt[A.Ind].Prio = APrio;
            F = A.Sub;
            while (F !is null)
            {
                if (auto nont = cast(EAG.Nont) F)
                    if (DefNonts[nont.Sym])
                    {
                        ++Alt[A.Ind].Deg;
                        NewEdge(nont.Sym, A.Ind);
                    }
                F = F.Next;
            }
            TestDeg(A.Ind);
            A = A.Next;
            ++APrio;
        }
        while (A !is null);
    }
    while (Top > 0)
    {
        Pop(E);
        while (E != nil)
        {
            --Alt[Edge[E].Dest].Deg;
            TestDeg(Edge[E].Dest);
            E = Edge[E].Next;
        }
    }
}

private void ComputeSets()
{
    BitArray Start;

    void NewGenSet(BitArray Toks, ref int GenSetIndex)
    {
        int i = firstGenSet;

        while (i < NextGenSet && GenSet[i] != Toks)
            ++i;
        GenSetIndex = i;
        if (i == NextGenSet)
        {
            if (NextGenSet >= GenSet.length)
                Expand;
            GenSet[NextGenSet] = Toks.dup;
            ++NextGenSet;
        }
    }

    void NewGenSetT(BitArray Toks, ref int GenSetTIndex)
    {
        int i = firstGenSetT;

        while (i < NextGenSetT && GenSetT[i] != Toks)
            ++i;
        GenSetTIndex = i;
        if (i == NextGenSetT)
        {
            if (NextGenSetT >= GenSetT.length)
                Expand;
            GenSetT[NextGenSetT] = Toks.dup;
            ++NextGenSetT;
        }
    }

    void ComputeRecoverySets(size_t N, ref BitArray LocalRec)
    {
        EAG.Alt A = EAG.HNont[N].Def.Sub;
        const RealAlt = A.Next !is null;
        EAG.Factor F;
        BitArray S;

        S.length = nToks + 1;
        do
        {
            if (cast(EAG.Rep) EAG.HNont[N].Def)
                S = LocalRec | Nont[N].First;
            else
                S = LocalRec.dup;
            F = A.Last;
            while (F !is null)
            {
                if (auto term = cast(EAG.Term) F)
                {
                    S[term.Sym - EAG.firstHTerm + firstUserTok] = true;
                    NewGenSet(S, Factor[F.Ind].Rec);
                }
                else if (auto nont = cast(EAG.Nont) F)
                {
                    if (GenNonts[nont.Sym])
                    {
                        if (!Nont[nont.Sym].Anonym)
                        {
                            if (UseReg && !RegNonts[N] && RegNonts[nont.Sym])
                                S[sepTok] = true;
                            NewGenSet(S, Factor[F.Ind].Rec);
                            S |= Nont[nont.Sym].First;
                        }
                        else
                        {
                            ComputeRecoverySets(nont.Sym, S);
                        }
                    }
                }
                F = F.Prev;
            }
            A = A.Next;
        }
        while (A !is null);
        LocalRec |= Nont[N].First;
        if (cast(EAG.Opt) EAG.HNont[N].Def || cast(EAG.Rep) EAG.HNont[N].Def)
            NewGenSet(LocalRec, Nont[N].OptRec);
        if (RealAlt)
            NewGenSet(LocalRec, Nont[N].AltRec);
    }

    Start = BitArray();
    Start.length = nToks + 1;
    foreach (N; GenNonts.bitsSet)
    {
        Start[] = false;
        if (N == EAG.StartSym)
            Start[endTok] = true;
        if (!Nont[N].Anonym)
            ComputeRecoverySets(N, Start);
        if (cast(EAG.Opt) EAG.HNont[N].Def || cast(EAG.Rep) EAG.HNont[N].Def)
        {
            if (!Nont[N].Anonym)
            {
                NewGenSet(Nont[N].First, Nont[N].OptExp);
            }
            else
            {
                Start = Nont[N].First | Nont[N].IniFollow;
                NewGenSet(Start, Nont[N].OptExp);
            }
            NewGenSetT(Nont[N].First, Nont[N].FirstIndex);
            NewGenSetT(Nont[N].Follow, Nont[N].FollowIndex);
        }
        if (EAG.HNont[N].Def.Sub.Next !is null)
            NewGenSet(Nont[N].First, Nont[N].AltExp);
    }
}

private string GenerateMod(Flag!"parsePass" parsePass, Settings settings)
{
    import std.stdio :File;

    File output;
    Input Fix;
    int Tok;
    BitArray AllToks;
    string name;
    long TabTimeStamp;
    size_t loopCount;

    void TraverseNont(size_t N, bool FirstNontCall, BitArray Poss)
    {
        bool ExactOneToken;
        int TheOneToken;

        void TraverseAlts(EAG.Alt A, bool FirstNontCall, BitArray Poss)
        {
            int Tok;
            BitArray Toks;
            bool FirstTok;

            void TraverseFactors(EAG.Factor F, bool FirstNontCall, BitArray Poss)
            {
                bool TwoCalls = false;
                BitArray Poss1 = Poss.dup;

                while (F !is null)
                {
                    if (auto term = cast(EAG.Term) F)
                    {
                        if (Poss1[term.Sym - EAG.firstHTerm + firstUserTok])
                        {
                            Poss1[term.Sym - EAG.firstHTerm + firstUserTok] = false;
                            if (Poss1.bitsSet.empty)
                            {
                                output.writeln("S.Get(Tok);");
                                output.writeln("IsRepairMode = false;");
                            }
                            else
                            {
                                output.write("if (Tok != ");
                                output.write(term.Sym - EAG.firstHTerm + firstUserTok);
                                output.writeln(")");
                                output.write("RecoveryTerminal(");
                                output.write(term.Sym - EAG.firstHTerm + firstUserTok);
                                output.write(", ");
                                output.write(Factor[F.Ind].Rec - firstGenSet);
                                output.writeln(");");
                                output.writeln("else");
                                output.writeln("{");
                                output.writeln("S.Get(Tok);");
                                output.writeln("IsRepairMode = false;");
                                output.writeln("}");
                            }
                        }
                        else
                        {
                            output.write("RecoveryTerminal(");
                            output.write(term.Sym - EAG.firstHTerm + firstUserTok);
                            output.write(", ");
                            output.write(Factor[F.Ind].Rec - firstGenSet);
                            output.writeln(");");
                        }
                        Poss1 = AllToks.dup;
                    }
                    else if (auto nont = cast(EAG.Nont) F)
                    {
                        if (GenNonts[nont.Sym])
                        {
                            EvalGen.GenSynPred(N, nont.Actual.Params);
                            if (!Nont[nont.Sym].Anonym)
                            {
                                if (FirstNontCall)
                                {
                                    output.writeln("if (RecTop >= RecStack.length) ParserExpand;");
                                    FirstNontCall = false;
                                }
                                if (TwoCalls)
                                    output.write("RecStack[RecTop - 1] = ");
                                else
                                    output.write("RecStack[RecTop] = ");
                                output.write(Factor[F.Ind].Rec - firstGenSet, ";");
                                if (!TwoCalls)
                                    output.writeln("++RecTop;");
                                if (UseReg && !RegNonts[N] && RegNonts[nont.Sym])
                                    output.writeln("S.Get = &S.Get3;");
                                output.write("P", nont.Sym);
                                EvalGen.GenActualParams(nont.Actual.Params, true);
                                output.writeln("; // ", EAG.HNontRepr(nont.Sym));
                                if (UseReg && !RegNonts[N] && RegNonts[nont.Sym])
                                {
                                    output.writeln("if (Tok == sepTok)");
                                    output.writeln("{");
                                    output.writeln("S.Get(Tok);");
                                    output.writeln("IsRepairMode = false;");
                                    output.writeln("}");
                                    output.writeln("S.Get = &S.Get2;");
                                }
                                if (F.Next !is null && cast(EAG.Nont) F.Next
                                        && GenNonts[(cast(EAG.Nont) F.Next).Sym]
                                        && !Nont[(cast(EAG.Nont) F.Next).Sym].Anonym)
                                    TwoCalls = true;
                                else
                                    TwoCalls = false;
                                if (!TwoCalls)
                                    output.writeln("--RecTop;");
                            }
                            else
                            {
                                TraverseNont(nont.Sym, FirstNontCall, Poss1);
                            }
                            EvalGen.GenAnalPred(N, nont.Actual.Params);
                            Poss1 = AllToks.dup;
                        }
                        else if (EAG.Pred[nont.Sym])
                        {
                            EvalGen.GenSynPred(N, nont.Actual.Params);
                            EvalGen.GenPredCall(nont.Sym, nont.Actual.Params);
                            EvalGen.GenAnalPred(N, nont.Actual.Params);
                        }
                        else
                        {
                            output.writeln(`throw new Exception("runtime error: call of nonproductive nonterminal!");`);
                            warn!"generated compiler contains corrupt code for non-productive nonterminals";
                            Warning = true;
                        }
                    }
                    F = F.Next;
                }
            }

            if (A.Next is null)
            {
                EvalGen.InitScope(A.Scope);
                EvalGen.GenAnalPred(N, A.Formal.Params);
                TraverseFactors(A.Sub, FirstNontCall, Poss);
                if (cast(EAG.Rep) EAG.HNont[N].Def)
                    EvalGen.GenRepAlt(N.to!int, A);
                else
                    EvalGen.GenSynPred(N, A.Formal.Params);
            }
            else
            {
                if (!EAG.Null[N])
                    Toks = Nont[N].First.dup;
                else
                    Toks = Nont[N].First | Nont[N].Follow;

                const LoopNeeded = !(Poss <= Toks);
                const label = format!"loop%s"(loopCount);

                if (LoopNeeded)
                {
                    ++loopCount;
                    output.writeln(label, ": while (1)");
                    output.writeln("{");
                }
                output.writeln("switch (Tok)");
                output.writeln("{");
                do
                {
                    if (!LoopNeeded && (Alt[A.Ind].Dir & Poss).bitsSet.empty)
                    {
                        warn!"dead alternative in %s\n%s"(EAG.NamedHNontRepr(N), A.Pos);
                        Warning = true;
                    }
                    output.write("case ");
                    FirstTok = true;
                    // foreach (Tok; Alt[A.Ind].Dir)
                    for (Tok = 0; Tok < nToks; ++Tok)
                    {
                        if (Alt[A.Ind].Dir[Tok])
                        {
                            if (!FirstTok)
                            {
                                output.writeln(":");
                                output.write("case ");
                            }
                            output.write(Tok);
                            FirstTok = false;
                        }
                    }
                    output.writeln(":");
                    EvalGen.InitScope(A.Scope);
                    EvalGen.GenAnalPred(N, A.Formal.Params);
                    TraverseFactors(A.Sub, FirstNontCall, Alt[A.Ind].Dir);
                    if (cast(EAG.Rep) EAG.HNont[N].Def)
                        EvalGen.GenRepAlt(N.to!int, A);
                    else
                        EvalGen.GenSynPred(N, A.Formal.Params);
                    if (LoopNeeded)
                        output.writeln("break ", label, ";");
                    else
                        output.writeln("break;");
                    A = A.Next;
                }
                while (A !is null);
                if (LoopNeeded)
                {
                    A = Nont[N].DefaultAlt;
                    output.writeln("default:");
                    output.writeln("if (IsRepairMode)");
                    output.writeln("{");
                    Toks = AllToks - Toks;
                    EvalGen.InitScope(A.Scope);
                    EvalGen.GenAnalPred(N, A.Formal.Params);
                    TraverseFactors(A.Sub, FirstNontCall, Toks);
                    if (cast(EAG.Rep) EAG.HNont[N].Def)
                        EvalGen.GenRepAlt(N.to!int, A);
                    else
                        EvalGen.GenSynPred(N, A.Formal.Params);
                    output.writeln("break ", label, ";");
                    output.writeln("}");
                    output.write("ErrorRecovery(");
                    output.write(Nont[N].AltExp - firstGenSet);
                    output.write(", ");
                    output.write(Nont[N].AltRec - firstGenSet);
                    output.writeln(");");
                }
                else
                {
                    output.writeln("default:");
                    output.writeln("assert(0);");
                }
                output.writeln("}");
                if (LoopNeeded)
                    output.writeln("}");
            }
        }

        void TestOneToken(BitArray Toks, ref bool ExactOneToken, ref int TheOneToken)
        {
            int Tok = 0;

            ExactOneToken = false;
            while (Tok < nToks)
            {
                if (Toks[Tok])
                {
                    if (ExactOneToken)
                    {
                        ExactOneToken = false;
                        return;
                    }
                    ExactOneToken = true;
                    TheOneToken = Tok;
                }
                ++Tok;
            }
        }

        if (auto opt = cast(EAG.Opt) EAG.HNont[N].Def)
        {
            if (Poss <= Nont[N].Follow && (Nont[N].First & Poss).bitsSet.empty)
            {
                warn!"dead brackets in %s\n%s"(EAG.NamedHNontRepr(N), EAG.HNont[N].Def.Sub.Pos);
                Warning = true;
            }
            else if (Poss <= Nont[N].First)
            {
                warn!"useless brackets in %s\n%s"(EAG.NamedHNontRepr(N), EAG.HNont[N].Def.Sub.Pos);
                Warning = true;
            }
            output.writeln("while (1)");
            output.writeln("{");
            output.write("if (");
            TestOneToken(Nont[N].First, ExactOneToken, TheOneToken);
            if (ExactOneToken)
            {
                output.write("Tok == ", TheOneToken);
            }
            else
            {
                output.write("SetT[");
                output.write(DIV(Nont[N].FirstIndex - firstGenSetT, nElemsPerSET));
                output.write("][Tok] & 1uL << ");
                output.write(MOD(Nont[N].FirstIndex - firstGenSetT, nElemsPerSET));
            }
            output.writeln(")");
            output.writeln("{");
            TraverseAlts(EAG.HNont[N].Def.Sub, FirstNontCall, Nont[N].First);
            output.writeln("break;");
            output.writeln("}");
            output.write("else if (");
            TestOneToken(Nont[N].Follow, ExactOneToken, TheOneToken);
            if (ExactOneToken)
            {
                output.write("Tok == ", TheOneToken);
            }
            else
            {
                output.write("SetT[");
                output.write(DIV(Nont[N].FollowIndex - firstGenSetT, nElemsPerSET));
                output.write("][Tok] & 1uL << ");
                output.write(MOD(Nont[N].FollowIndex - firstGenSetT, nElemsPerSET));
            }
            output.writeln(" || IsRepairMode)");
            output.writeln("{");
            EvalGen.InitScope(opt.Scope);
            EvalGen.GenAnalPred(N, opt.Formal.Params);
            EvalGen.GenSynPred(N, opt.Formal.Params);
            output.writeln("break;");
            output.writeln("}");
            output.write("ErrorRecovery(");
            output.write(Nont[N].OptExp - firstGenSet);
            output.write(", ");
            output.write(Nont[N].OptRec - firstGenSet);
            output.writeln(");");
            output.writeln("}");
        }
        else if (cast(EAG.Rep) EAG.HNont[N].Def)
        {
            if (Poss <= Nont[N].Follow && (Nont[N].First & Poss).bitsSet.empty)
            {
                warn!"dead braces in %s\n%s"(EAG.NamedHNontRepr(N), EAG.HNont[N].Def.Sub.Pos);
                Warning = true;
            }
            EvalGen.GenRepStart(N.to!int);
            output.writeln("while (1)");
            output.writeln("{");
            output.write("if (");
            TestOneToken(Nont[N].First, ExactOneToken, TheOneToken);
            if (ExactOneToken)
            {
                output.write("Tok == ", TheOneToken);
            }
            else
            {
                output.write("SetT[");
                output.write(DIV(Nont[N].FirstIndex - firstGenSetT, nElemsPerSET));
                output.write("][Tok] & 1uL << ");
                output.write(MOD(Nont[N].FirstIndex - firstGenSetT, nElemsPerSET));
           }
            output.writeln(")");
            output.writeln("{");
            TraverseAlts(EAG.HNont[N].Def.Sub, FirstNontCall, Nont[N].First);
            output.writeln("}");
            output.write("else if (");
            TestOneToken(Nont[N].Follow, ExactOneToken, TheOneToken);
            if (ExactOneToken)
            {
                output.write("Tok == ", TheOneToken);
            }
            else
            {
                output.write("SetT[");
                output.write(DIV(Nont[N].FollowIndex - firstGenSetT, nElemsPerSET));
                output.write("][Tok] & 1uL << ");
                output.write(MOD(Nont[N].FollowIndex - firstGenSetT, nElemsPerSET));
            }
            output.writeln(" || IsRepairMode)");
            output.writeln("break;");
            output.writeln("else");
            output.writeln("ErrorRecovery(", Nont[N].OptExp - firstGenSet, ", ", Nont[N].OptRec - firstGenSet, ");");
            output.writeln("}");
            EvalGen.GenRepEnd(N.to!int);
        }
        else
        {
            TraverseAlts(EAG.HNont[N].Def.Sub, FirstNontCall, Poss);
        }
    }

    void WriteTab(string name)
    {
        const magicNumber = 827_092_037;
        size_t m;
        File Tab = File(settings.outputPath(name), "w");

        Tab.writefln!"long %s"(magicNumber);
        Tab.writefln!"long %s"(TabTimeStamp);
        Tab.writefln!"long %s"(nElemsPerSET);
        Tab.writefln!"set %s"(0b10110010_01000100_00111000_11011001);
        for (size_t i = firstGenSetT; i < NextGenSetT; i += nElemsPerSET)
        {
            if (nElemsPerSET <= NextGenSetT - i)
                m = nElemsPerSET;
            else
                m = NextGenSetT - i;
            for (int Tok = 0; Tok < nToks; ++Tok)
            {
                size_t s = 0;

                for (size_t j = 0; j < m; ++j)
                    if (GenSetT[i + j][Tok])
                        s |= 1uL << j;
                Tab.writefln!"set %s"(s);
            }
        }
        for (size_t i = firstGenSet; i < NextGenSet; ++i)
        {
            const data = cast(size_t[]) GenSet[i];

            for (int j = 0; j < GenSet[i].dim; ++j)
                Tab.writefln!"set %s"(data[j]);
        }
        Tab.writefln!"long %s"(magicNumber);
    }

    void InclFix(char Term)
    {
        import std.exception : enforce;

        char c = Fix.front.to!char;

        while (c != Term)
        {
            enforce(c != 0,
                    "error: unexpected end of eELL1Gen.fix.d");

            output.write(c);
            Fix.popFront;
            c = Fix.front.to!char;
        }
        Fix.popFront;
    }

    enum fixName = "ell1gen.fix.d";
    const fileName = settings.path(EAG.BaseName ~ ".d");

    AllToks = BitArray();
    AllToks.length = nToks + 1;
    Fix = Input(fixName, import(fixName));
    output = File(fileName, "w");
    if (parsePass)
        EvalGen.InitGen(output, EvalGen.parsePass, settings);
    else
        EvalGen.InitGen(output, EvalGen.onePass, settings);
    InclFix('$');
    output.write(EAG.BaseName);
    InclFix('$');
    name = EAG.BaseName ~ "Lex";
    output.write(name);
    if (parsePass)
    {
        output.write(", Eval = ");
        output.write(EAG.BaseName);
        output.write("Eval");
    }
    InclFix('$');
    output.write(nToks);
    InclFix('$');
    output.write(AllToks.dim);
    InclFix('$');
    output.write(DIV(NextGenSetT - firstGenSetT - 1, nElemsPerSET) + 1);
    InclFix('$');
    output.write(NextGenSet - firstGenSet);
    InclFix('$');
    EvalGen.GenDeclarations(settings);
    EvalGen.GenPredProcs;
    InclFix('$');
    TabTimeStamp = MonoTime.currTime.ticks;
    output.write(TabTimeStamp);
    InclFix('$');
    AllToks[] = false;
    for (Tok = 0; Tok < nToks; ++Tok)
        AllToks[Tok] = true; // TODO: opSliceAssign
    foreach (N; GenNonts.bitsSet)
    {
        if (!Nont[N].Anonym)
        {
            loopCount = 0;
            EvalGen.ComputeVarNames(N, Yes.embed);
            output.write("void P", N);
            EvalGen.GenFormalParams(N, Yes.parNeeded);
            output.writeln(" // ", EAG.HNontRepr(N));
            output.writeln("{");
            EvalGen.GenVarDecl(N);
            TraverseNont(N, true, AllToks);
            output.writeln("}");
            output.writeln;
        }
    }
    if (!parsePass)
        EmitGen.GenEmitProc(output, settings);
    InclFix('$');
    if (parsePass)
        output.write("& Eval.EvalInitSucceeds()");
    InclFix('$');
    output.write(EAG.BaseName);
    InclFix('$');
    output.write("P");
    output.write(EAG.StartSym);
    InclFix('$');
    if (parsePass)
    {
        output.writeln("Eval.TraverseSyntaxTree(Heap, PosHeap, ErrorCounter, V1, arityConst, info_, write);");
        output.writeln("if (info_)");
        output.writeln("{");
        output.writeln(`stdout.write("    syntax tree uses twice ");`);
        output.writeln("stdout.write(NextHeap);");
        output.writeln("stdout.writeln;");
        output.write("}");
    }
    else
    {
        output.writeln("if (ErrorCounter > 0)");
        output.writeln("{");
        output.writeln("import core.stdc.stdlib : exit, EXIT_FAILURE;");
        output.writeln(`info!"errors detected: %s"(ErrorCounter);`);
        output.writeln("exit(EXIT_FAILURE);");
        output.writeln("}");
        output.writeln("else");
        output.writeln("{");
        EmitGen.GenEmitCall(output, settings);
        output.writeln("}");
        EmitGen.GenShowHeap(output);
    }
    InclFix('$');
    output.write(EAG.BaseName);
    InclFix('$');
    name = EAG.BaseName ~ ".Tab";
    output.write(name);
    InclFix('$');
    output.write(EAG.BaseName);
    InclFix('$');
    name = EAG.BaseName ~ ".Tab";
    WriteTab(name);
    EvalGen.FinitGen;
    output.close;
    return fileName;
}

private void NewEdge(size_t From, int To) nothrow @safe
{
    if (NextEdge == Edge.length)
        Expand;
    Edge[NextEdge].Dest = To;
    Edge[NextEdge].Next = Nont[From].Edge;
    Nont[From].Edge = NextEdge;
    ++NextEdge;
}

private void Expand() nothrow @safe
{
    size_t ExpLen(size_t ArrayLen)
    {
        assert(ArrayLen <= DIV(size_t.max, 2));

        return 2 * ArrayLen;
    }

    if (NextEdge >= Edge.length)
    {
        auto Edge1 = new EdgeRecord[ExpLen(Edge.length)];

        for (size_t i = firstEdge; i < Edge.length; ++i)
            Edge1[i] = Edge[i];
        Edge = Edge1;
    }
    if (NextGenSet >= GenSet.length)
    {
        auto GenSet1 = new BitArray[ExpLen(GenSet.length)];

        for (size_t i = firstGenSet; i < GenSet.length; ++i)
            GenSet1[i] = GenSet[i];
        GenSet = GenSet1;
    }
    if (NextGenSetT >= GenSetT.length)
    {
        auto GenSetT1 = new BitArray[ExpLen(GenSetT.length)];

        for (size_t i = firstGenSetT; i < GenSetT.length; ++i)
            GenSetT1[i] = GenSetT[i];
        GenSetT = GenSetT1;
    }
}

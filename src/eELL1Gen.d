module eELL1Gen;

import runtime;
import Sets = eSets;
import IO = eIO;
import EAG = eEAG;
import EvalGen = eSLEAGGen;
import EmitGen = eEmitGen;
import Shift = eShift;
import io : Position, TextIn;
import std.stdio;

const nil = 0;
const endTok = 0;
const undefTok = 1;
const sepTok = 2;
const firstUserTok = 3;
const nElemsPerSET = 31 + 1;
const firstEdge = 1;
const firstGenSet = 1;
const firstGenSetT = 1;

struct NontRecord
{
    Sets.OpenSet First;
    Sets.OpenSet Follow;
    Sets.OpenSet IniFollow;
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

alias OpenNont = NontRecord[];

struct AltRecord
{
    Sets.OpenSet Dir;
}

alias OpenAlt = AltRecord[];

struct FactorRecord
{
    int Rec;
}

alias OpenFactor = FactorRecord[];

struct EdgeRecord
{
    int Dest;
    int Next;
}

alias OpenEdge = EdgeRecord[];
alias OpenGenSet = Sets.OpenSet[];
alias OpenGenSetT = Sets.OpenSet[];
OpenNont Nont;
OpenAlt Alt;
OpenFactor Factor;
OpenEdge Edge;
int NextEdge;
OpenGenSet GenSet;
int NextGenSet;
OpenGenSetT GenSetT;
int NextGenSetT;
Sets.OpenSet TestNonts;
Sets.OpenSet GenNonts;
Sets.OpenSet RegNonts;
Sets.OpenSet ConflictNonts;
int nToks;
bool Error;
bool Warning;
bool ShowMod;
bool Compiled;
bool UseReg;

void Expand()
{
    OpenEdge Edge1;
    OpenGenSet GenSet1;
    OpenGenSetT GenSetT1;
    long i;

    long ExpLen(long ArrayLen)
    {
        if (ArrayLen <= DIV(int.max, 2))
        {
            return 2 * ArrayLen;
        }
        else
        {
            assert(0);
        }
    }

    if (NextEdge >= Edge.length)
    {
        NEW(Edge1, ExpLen(Edge.length));
        for (i = firstEdge; i <= Edge.length - 1; ++i)
        {
            Edge1[i] = Edge[i];
        }
        Edge = Edge1;
    }
    if (NextGenSet >= GenSet.length)
    {
        NEW(GenSet1, ExpLen(GenSet.length));
        for (i = firstGenSet; i <= GenSet.length - 1; ++i)
        {
            GenSet1[i] = GenSet[i];
        }
        GenSet = GenSet1;
    }
    if (NextGenSetT >= GenSetT.length)
    {
        NEW(GenSetT1, ExpLen(GenSetT.length));
        for (i = firstGenSetT; i <= GenSetT.length - 1; ++i)
        {
            GenSetT1[i] = GenSetT[i];
        }
        GenSetT = GenSetT1;
    }
}
/**
 * R  whole procedure
 */
void ComputeRegNonts()
{
    int N;
    EAG.Alt A;
    EAG.Factor F;
    void TraverseRegNonts(int N)
    {
        EAG.Alt A;
        EAG.Factor F;
        A = EAG.HNont[N].Def.Sub;
        do
        {
            F = A.Sub;
            while (F !is null)
            {
                if (cast(EAG.Nont) F !is null
                        && Sets.In(TestNonts, (cast(EAG.Nont) F).Sym)
                        && !Sets.In(RegNonts, (cast(EAG.Nont) F).Sym))
                {
                    Sets.Incl(RegNonts, (cast(EAG.Nont) F).Sym);
                    TraverseRegNonts((cast(EAG.Nont) F).Sym);
                }
                F = F.Next;
            }
            A = A.Next;
        }
        while (A !is null);
    }

    void DeleteConflictNont(int N)
    {
        EAG.Alt A;
        EAG.Factor F;
        Sets.Excl(ConflictNonts, N);
        A = EAG.HNont[N].Def.Sub;
        do
        {
            F = A.Sub;
            while (F !is null)
            {
                if (cast(EAG.Nont) F !is null && Sets.In(ConflictNonts, (cast(EAG.Nont) F).Sym))
                {
                    DeleteConflictNont((cast(EAG.Nont) F).Sym);
                }
                F = F.Next;
            }
            A = A.Next;
        }
        while (A !is null);
    }

    Sets.Empty(RegNonts);
    for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
    {
        if (Sets.In(TestNonts, N) && EAG.HNont[N].IsToken && !Sets.In(RegNonts, N))
        {
            Sets.Incl(RegNonts, N);
            TraverseRegNonts(N);
        }
    }
    Sets.Assign(ConflictNonts, RegNonts);
    for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
    {
        if (Sets.In(ConflictNonts, N))
        {
            A = EAG.HNont[N].Def.Sub;
            do
            {
                F = A.Last;
                while (F !is null && cast(EAG.Nont) F !is null && !Sets.In(TestNonts, (cast(EAG.Nont) F).Sym))
                {
                    F = F.Prev;
                }
                if (F !is null)
                {
                    F = F.Prev;
                }
                while (F !is null)
                {
                    if (cast(EAG.Nont) F !is null && Sets.In(ConflictNonts, (cast(EAG.Nont) F).Sym))
                    {
                        DeleteConflictNont((cast(EAG.Nont) F).Sym);
                    }
                    F = F.Prev;
                }
                A = A.Next;
            }
            while (A !is null);
        }
    }
}

void Init()
{
    int i;
    nToks = EAG.NextHTerm - EAG.firstHTerm + firstUserTok;
    if (EAG.NextHNont >= 1)
    {
        NEW(Nont, EAG.NextHNont);
    }
    else
    {
        NEW(Nont, 1);
    }
    for (i = EAG.firstHNont; i <= EAG.NextHNont - 1; ++i)
    {
        Sets.New(Nont[i].First, nToks);
        Sets.New(Nont[i].Follow, nToks);
        Sets.New(Nont[i].IniFollow, nToks);
        Nont[i].DefaultAlt = null;
        Nont[i].AltRec = nil;
        Nont[i].OptRec = nil;
        Nont[i].AltExp = nil;
        Nont[i].OptExp = nil;
        Nont[i].FirstIndex = nil;
        Nont[i].FollowIndex = nil;
        Nont[i].Anonym = Sets.In(EAG.All, i) && EAG.HNont[i].Id < 0;
    }
    if (EAG.NextHAlt >= 1)
    {
        NEW(Alt, EAG.NextHAlt);
    }
    else
    {
        NEW(Alt, 1);
    }
    for (i = EAG.firstHAlt; i <= EAG.NextHAlt - 1; ++i)
    {
        Sets.New(Alt[i].Dir, nToks);
    }
    if (EAG.NextHFactor >= 1)
    {
        NEW(Factor, EAG.NextHFactor);
    }
    else
    {
        NEW(Factor, 1);
    }
    for (i = EAG.firstHFactor; i <= EAG.NextHFactor - 1; ++i)
    {
        Factor[i].Rec = nil;
    }
    NEW(Edge, 255);
    NextEdge = firstEdge;
    NEW(GenSet, 511);
    NextGenSet = firstGenSet;
    NEW(GenSetT, 255);
    NextGenSetT = firstGenSetT;
    Sets.New(TestNonts, EAG.NextHNont);
    Sets.Difference(TestNonts, EAG.All, EAG.Pred);
    Sets.New(GenNonts, EAG.NextHNont);
    Sets.Intersection(GenNonts, EAG.Prod, EAG.Reach);
    Sets.Difference(GenNonts, GenNonts, EAG.Pred);
    Error = false;
    Warning = false;
    ShowMod = IO.IsOption('m');
    UseReg = !IO.IsOption('p');
    Sets.New(RegNonts, EAG.NextHNont);
    Sets.New(ConflictNonts, EAG.NextHNont);
    if (UseReg)
    {
        ComputeRegNonts;
    }
}

void Finit()
{
    Nont = null;
    Alt = null;
    Factor = null;
    Edge = null;
    GenSet = null;
    GenSetT = null;
}

void WriteTok(IO.TextOut Out, int Tok)
{
    if (Tok == endTok)
    {
        IO.WriteText(Out, "!end!");
    }
    else if (Tok == undefTok)
    {
        IO.WriteText(Out, "!undef!");
    }
    else if (Tok == sepTok)
    {
        IO.WriteText(Out, "!sep!");
    }
    else
    {
        EAG.WriteHTerm(Out, Tok + EAG.firstHTerm - firstUserTok);
    }
}

void WriteTokSet(IO.TextOut Out, Sets.OpenSet Toks)
{
    int Tok;
    for (Tok = 0; Tok <= nToks - 1; ++Tok)
    {
        if (Sets.In(Toks, Tok))
        {
            WriteTok(Out, Tok);
            IO.WriteText(Out, " ");
        }
    }
}

void NewEdge(int From, int To)
{
    if (NextEdge == Edge.length)
    {
        Expand;
    }
    Edge[NextEdge].Dest = To;
    Edge[NextEdge].Next = Nont[From].Edge;
    Nont[From].Edge = NextEdge;
    ++NextEdge;
}
/**
 * R  whole procedure
 */
bool GrammarOk()
{
    int N;
    EAG.Alt A;
    EAG.Factor F;
    bool Ok;
    Ok = true;
    if (UseReg)
    {
        if (Sets.In(RegNonts, EAG.StartSym))
        {
            if (EAG.HNont[EAG.StartSym].IsToken)
            {
                IO.WriteText(IO.Msg, "\n  start symbol must not be a token");
            }
            else
            {
                IO.WriteText(IO.Msg, "\n  start symbol must not be a subtoken");
            }
            IO.Update(IO.Msg);
            Ok = false;
        }
        for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
        {
            if (Sets.In(TestNonts, N) && EAG.HNont[N].IsToken)
            {
                if (Sets.In(EAG.Null, N))
                {
                    IO.WriteText(IO.Msg, "\n  marked token ");
                    EAG.WriteHNont(IO.Msg, N);
                    IO.WriteText(IO.Msg, " is nullable");
                    IO.Update(IO.Msg);
                    Ok = false;
                }
                if (Nont[N].Anonym)
                {
                    IO.WriteText(IO.Msg, "\n  internal error: token in ");
                    EAG.WriteNamedHNont(IO.Msg, N);
                    IO.WriteText(IO.Msg, " is anonym");
                    IO.Update(IO.Msg);
                    Ok = false;
                }
            }
        }
        for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
        {
            if (Sets.In(TestNonts, N) && !Sets.In(RegNonts, N))
            {
                A = EAG.HNont[N].Def.Sub;
                do
                {
                    F = A.Sub;
                    while (F !is null)
                    {
                        if (cast(EAG.Nont) F !is null && Sets.In(TestNonts, (cast(EAG.Nont) F).Sym)
                                && Sets.In(RegNonts, (cast(EAG.Nont) F).Sym)
                                && !EAG.HNont[(cast(EAG.Nont) F).Sym].IsToken)
                        {
                            IO.WriteText(IO.Msg, "\n  nonterminal ");
                            if (Nont[N].Anonym)
                            {
                                IO.WriteText(IO.Msg, "in ");
                            }
                            EAG.WriteNamedHNont(IO.Msg, N);
                            IO.WriteText(IO.Msg, " calls subtoken ");
                            EAG.WriteHNont(IO.Msg, (cast(EAG.Nont) F).Sym);
                            IO.Update(IO.Msg);
                            Ok = false;
                        }
                        F = F.Next;
                    }
                    A = A.Next;
                }
                while (A !is null);
            }
        }
    }
    return Ok;
}

void ComputeDir()
{
    int N;
    EAG.Alt A;
    EAG.Factor F;
    int[] State;
    int[] Stack;
    int Top;
    Sets.OpenSet NullAlts;
    Sets.OpenSet Toks;
    bool IsLast;
    void ComputeFirst(int N)
    {
        int n;
        int E;
        int N1;
        bool Leftrecursion;
        Stack[Top] = N;
        ++Top;
        n = Top;
        State[N] = n;
        E = Nont[N].Edge;
        Leftrecursion = false;
        while (E != nil)
        {
            N1 = Edge[E].Dest;
            if (N1 == N)
            {
                Leftrecursion = true;
            }
            if (State[N1] == 0)
            {
                ComputeFirst(N1);
            }
            if (State[N1] < State[N])
            {
                State[N] = State[N1];
            }
            Sets.Union(Nont[N].First, Nont[N].First, Nont[N1].First);
            E = Edge[E].Next;
        }
        if (State[N] == n)
        {
            Leftrecursion = Leftrecursion || Top > n;
            if (Leftrecursion)
            {
                Error = true;
                IO.WriteText(IO.Msg, "\n  left recursion over nonterminals:");
            }
            do
            {
                --Top;
                N1 = Stack[Top];
                State[N1] = int.max;
                if (Leftrecursion)
                {
                    IO.WriteText(IO.Msg, "\n    ");
                    EAG.WriteNamedHNont(IO.Msg, N1);
                    if (Nont[N1].Anonym)
                    {
                        IO.WriteText(IO.Msg, " (EBNF at ");
                        writeln;
                        writeln(EAG.HNont[N1].Def.Sub.Pos);
                        IO.WriteText(IO.Msg, ")");
                    }
                }
                Nont[N1].First = Nont[N].First;
            }
            while (!(Top < n));
            if (Leftrecursion)
            {
                IO.Update(IO.Msg);
            }
        }
    }

    void ComputeFollow(int N)
    {
        int n;
        int E;
        int N1;
        Stack[Top] = N;
        ++Top;
        n = Top;
        State[N] = n;
        E = Nont[N].Edge;
        while (E != nil)
        {
            N1 = Edge[E].Dest;
            if (State[N1] == 0)
            {
                ComputeFollow(N1);
            }
            if (State[N1] < State[N])
            {
                State[N] = State[N1];
            }
            Sets.Union(Nont[N].Follow, Nont[N].Follow, Nont[N1].Follow);
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
            while (!(Top < n));
        }
    }

    void Conflict(int N, Position Pos, Sets.OpenSet Dir, Sets.OpenSet PrevDirs)
    {
        Sets.OpenSet Toks;
        Warning = true;
        Sets.New(Toks, nToks);
        writeln;
        writeln(Pos);
        IO.WriteText(IO.Msg, "  director set conflict in ");
        EAG.WriteNamedHNont(IO.Msg, N);
        IO.WriteText(IO.Msg, ": ");
        Sets.Intersection(Toks, Dir, PrevDirs);
        WriteTokSet(IO.Msg, Toks);
        Sets.Difference(Toks, Dir, PrevDirs);
        if (Sets.IsEmpty(Toks))
        {
            Error = true;
            IO.WriteText(IO.Msg, "\n    alternative will never be chosen");
        }
        IO.Update(IO.Msg);
    }

    NEW(State, EAG.NextHNont);
    NEW(Stack, EAG.NextHNont);
    Top = 0;
    Sets.New(NullAlts, EAG.NextHAlt);
    Sets.New(Toks, nToks);
    NextEdge = firstEdge;
    for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
    {
        Nont[N].Edge = nil;
        State[N] = 0;
    }
    for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
    {
        if (Sets.In(TestNonts, N))
        {
            Sets.Empty(Nont[N].First);
            A = EAG.HNont[N].Def.Sub;
            do
            {
                F = A.Sub;
                while (true)
                {
                    if (F is null)
                    {
                        break;
                    }
                    if (cast(EAG.Term) F !is null)
                    {
                        Sets.Incl(Nont[N].First, (cast(EAG.Term) F).Sym - EAG.firstHTerm + firstUserTok);
                        break;
                    }
                    else
                    {
                        if (Sets.In(TestNonts, (cast(EAG.Nont) F).Sym))
                        {
                            NewEdge(N, (cast(EAG.Nont) F).Sym);
                            if (!Sets.In(EAG.Null, (cast(EAG.Nont) F).Sym))
                            {
                                break;
                            }
                        }
                    }
                    F = F.Next;
                }
                A = A.Next;
            }
            while (A !is null);
        }
    }
    for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
    {
        if (Sets.In(TestNonts, N) && State[N] == 0)
        {
            ComputeFirst(N);
        }
    }
    NextEdge = firstEdge;
    for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
    {
        Nont[N].Edge = nil;
        Sets.Empty(Nont[N].Follow);
    }
    Sets.Incl(Nont[EAG.StartSym].Follow, endTok);
    Sets.Empty(NullAlts);
    for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
    {
        if (Sets.In(TestNonts, N))
        {
            A = EAG.HNont[N].Def.Sub;
            do
            {
                if (cast(EAG.Rep) EAG.HNont[N].Def !is null)
                {
                    Sets.Assign(Toks, Nont[N].First);
                }
                else
                {
                    Sets.Empty(Toks);
                }
                F = A.Last;
                IsLast = true;
                while (F !is null)
                {
                    if (cast(EAG.Term) F !is null)
                    {
                        Sets.Empty(Toks);
                        Sets.Incl(Toks, (cast(EAG.Term) F).Sym - EAG.firstHTerm + firstUserTok);
                        IsLast = false;
                    }
                    else
                    {
                        if (Sets.In(TestNonts, (cast(EAG.Nont) F).Sym))
                        {
                            if (IsLast)
                            {
                                NewEdge((cast(EAG.Nont) F).Sym, N);
                            }
                            Sets.Union(Nont[(cast(EAG.Nont) F).Sym].Follow,
                                    Nont[(cast(EAG.Nont) F).Sym].Follow, Toks);
                            if (UseReg && !Sets.In(RegNonts, N)
                                    && Sets.In(RegNonts, (cast(EAG.Nont) F).Sym))
                            {
                                Sets.Incl(Nont[(cast(EAG.Nont) F).Sym].Follow, sepTok);
                            }
                            if (Sets.In(EAG.Null, (cast(EAG.Nont) F).Sym))
                            {
                                Sets.Union(Toks, Toks, Nont[(cast(EAG.Nont) F).Sym].First);
                            }
                            else
                            {
                                Sets.Assign(Toks, Nont[(cast(EAG.Nont) F).Sym].First);
                                IsLast = false;
                            }
                        }
                    }
                    F = F.Prev;
                }
                if (IsLast)
                {
                    Sets.Incl(NullAlts, A.Ind);
                }
                A = A.Next;
            }
            while (A !is null);
        }
    }
    for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
    {
        if (Sets.In(TestNonts, N))
        {
            Sets.Assign(Nont[N].IniFollow, Nont[N].Follow);
        }
    }
    for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
    {
        State[N] = 0;
    }
    for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
    {
        if (Sets.In(TestNonts, N) && State[N] == 0)
        {
            ComputeFollow(N);
        }
    }
    for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
    {
        if (Sets.In(TestNonts, N))
        {
            Sets.Empty(Toks);
            A = EAG.HNont[N].Def.Sub;
            do
            {
                if (Sets.In(NullAlts, A.Ind))
                {
                    Sets.Assign(Alt[A.Ind].Dir, Nont[N].Follow);
                }
                else
                {
                    Sets.Empty(Alt[A.Ind].Dir);
                }
                F = A.Sub;
                while (true)
                {
                    if (F is null)
                    {
                        break;
                    }
                    if (cast(EAG.Term) F !is null)
                    {
                        Sets.Incl(Alt[A.Ind].Dir, (cast(EAG.Term) F).Sym - EAG.firstHTerm + firstUserTok);
                        break;
                    }
                    else
                    {
                        if (Sets.In(TestNonts, (cast(EAG.Nont) F).Sym))
                        {
                            Sets.Union(Alt[A.Ind].Dir, Alt[A.Ind].Dir,
                                    Nont[(cast(EAG.Nont) F).Sym].First);
                            if (!Sets.In(EAG.Null, (cast(EAG.Nont) F).Sym))
                            {
                                break;
                            }
                        }
                    }
                    F = F.Next;
                }
                if (!Sets.Disjoint(Alt[A.Ind].Dir, Toks))
                {
                    Conflict(N, A.Pos, Alt[A.Ind].Dir, Toks);
                    Sets.Difference(Alt[A.Ind].Dir, Alt[A.Ind].Dir, Toks);
                }
                Sets.Union(Toks, Toks, Alt[A.Ind].Dir);
                A = A.Next;
            }
            while (A !is null);
            if (cast(EAG.Opt) EAG.HNont[N].Def !is null || cast(EAG.Rep) EAG.HNont[N].Def !is null)
            {
                if (!Sets.Disjoint(Nont[N].Follow, Toks))
                {
                    if (!UseReg || !Sets.In(ConflictNonts, N) || Sets.In(Toks, sepTok))
                    {
                        if (cast(EAG.Opt) EAG.HNont[N].Def !is null)
                        {
                            Conflict(N, (cast(EAG.Opt) EAG.HNont[N].Def)
                                    .EmptyAltPos, Nont[N].Follow, Toks);
                        }
                        else
                        {
                            Conflict(N, (cast(EAG.Rep) EAG.HNont[N].Def)
                                    .EmptyAltPos, Nont[N].Follow, Toks);
                        }
                    }
                }
            }
        }
    }
}

void ComputeDefaultAlts()
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

    int N;
    EAG.Alt A;
    EAG.Factor F;
    int E;
    int APrio;
    AltRecord[] Alt;
    StackRecord[] Stack;
    int Top;
    int[] StackPos;
    Sets.OpenSet DefNonts;
    void TestDeg(int AInd)
    {
        int N;
        int i;
        if (Alt[AInd].Deg == 0)
        {
            N = Alt[AInd].Nont;
            i = StackPos[N];
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
        while (!(i == 0 || MinPrio == 1));
        Nont[Stack[MinPos].Nont].DefaultAlt = Stack[MinPos].Alt;
        Edge = Nont[Stack[MinPos].Nont].Edge;
        StackPos[Stack[Top].Nont] = MinPos;
        StackPos[Stack[MinPos].Nont] = -1;
        Stack[MinPos] = Stack[Top];
    }

    if (EAG.NextHAlt >= 1)
    {
        NEW(Alt, EAG.NextHAlt);
    }
    if (EAG.NextHNont >= 1)
    {
        NEW(Stack, EAG.NextHNont);
    }
    Top = 0;
    if (EAG.NextHNont >= 1)
    {
        NEW(StackPos, EAG.NextHNont);
    }
    Sets.New(DefNonts, EAG.NextHNont);
    Sets.Assign(DefNonts, GenNonts);
    NextEdge = firstEdge;
    for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
    {
        Nont[N].Edge = nil;
        Nont[N].DefaultAlt = null;
        StackPos[N] = int.max;
        if (Sets.In(GenNonts, N)
                && (cast(EAG.Opt) EAG.HNont[N].Def !is null || cast(EAG.Rep) EAG.HNont[N].Def !is null))
        {
            Sets.Excl(DefNonts, N);
        }
    }
    for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
    {
        if (Sets.In(DefNonts, N))
        {
            A = EAG.HNont[N].Def.Sub;
            APrio = 1;
            do
            {
                Alt[A.Ind].Nont = N;
                Alt[A.Ind].Alt = A;
                Alt[A.Ind].Deg = 0;
                Alt[A.Ind].Prio = APrio;
                F = A.Sub;
                while (F !is null)
                {
                    if (cast(EAG.Nont) F !is null && Sets.In(DefNonts, (cast(EAG.Nont) F).Sym))
                    {
                        ++Alt[A.Ind].Deg;
                        NewEdge((cast(EAG.Nont) F).Sym, A.Ind);
                    }
                    F = F.Next;
                }
                TestDeg(A.Ind);
                A = A.Next;
                ++APrio;
            }
            while (A !is null);
        }
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

void ComputeSets()
{
    int N;
    Sets.OpenSet Start;
    void NewGenSet(Sets.OpenSet Toks, ref int GenSetIndex)
    {
        int i;
        i = firstGenSet;
        while (i < NextGenSet && !Sets.Equal(GenSet[i], Toks))
        {
            ++i;
        }
        GenSetIndex = i;
        if (i == NextGenSet)
        {
            if (NextGenSet >= GenSet.length)
            {
                Expand;
            }
            Sets.New(GenSet[NextGenSet], nToks);
            Sets.Assign(GenSet[NextGenSet], Toks);
            ++NextGenSet;
        }
    }

    void NewGenSetT(Sets.OpenSet Toks, ref int GenSetTIndex)
    {
        int i;
        i = firstGenSetT;
        while (i < NextGenSetT && !Sets.Equal(GenSetT[i], Toks))
        {
            ++i;
        }
        GenSetTIndex = i;
        if (i == NextGenSetT)
        {
            if (NextGenSetT >= GenSetT.length)
            {
                Expand;
            }
            Sets.New(GenSetT[NextGenSetT], nToks);
            Sets.Assign(GenSetT[NextGenSetT], Toks);
            ++NextGenSetT;
        }
    }

    void ComputeRecoverySets(int N, ref Sets.OpenSet LocalRec)
    {
        EAG.Alt A;
        EAG.Factor F;
        Sets.OpenSet S;
        bool RealAlt;
        Sets.New(S, nToks);
        A = EAG.HNont[N].Def.Sub;
        RealAlt = A.Next !is null;
        do
        {
            if (cast(EAG.Rep) EAG.HNont[N].Def !is null)
            {
                Sets.Union(S, LocalRec, Nont[N].First);
            }
            else
            {
                Sets.Assign(S, LocalRec);
            }
            F = A.Last;
            while (F !is null)
            {
                if (cast(EAG.Term) F !is null)
                {
                    Sets.Incl(S, (cast(EAG.Term) F).Sym - EAG.firstHTerm + firstUserTok);
                    NewGenSet(S, Factor[F.Ind].Rec);
                }
                else
                {
                    if (Sets.In(GenNonts, (cast(EAG.Nont) F).Sym))
                    {
                        if (!Nont[(cast(EAG.Nont) F).Sym].Anonym)
                        {
                            if (UseReg && !Sets.In(RegNonts, N)
                                    && Sets.In(RegNonts, (cast(EAG.Nont) F).Sym))
                            {
                                Sets.Incl(S, sepTok);
                            }
                            NewGenSet(S, Factor[F.Ind].Rec);
                            Sets.Union(S, S, Nont[(cast(EAG.Nont) F).Sym].First);
                        }
                        else
                        {
                            ComputeRecoverySets((cast(EAG.Nont) F).Sym, S);
                        }
                    }
                }
                F = F.Prev;
            }
            A = A.Next;
        }
        while (A !is null);
        Sets.Union(LocalRec, LocalRec, Nont[N].First);
        if (cast(EAG.Opt) EAG.HNont[N].Def !is null || cast(EAG.Rep) EAG.HNont[N].Def !is null)
        {
            NewGenSet(LocalRec, Nont[N].OptRec);
        }
        if (RealAlt)
        {
            NewGenSet(LocalRec, Nont[N].AltRec);
        }
    }

    Sets.New(Start, nToks);
    for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
    {
        if (Sets.In(GenNonts, N))
        {
            Sets.Empty(Start);
            if (N == EAG.StartSym)
            {
                Sets.Incl(Start, endTok);
            }
            if (!Nont[N].Anonym)
            {
                ComputeRecoverySets(N, Start);
            }
            if (cast(EAG.Opt) EAG.HNont[N].Def !is null || cast(EAG.Rep) EAG.HNont[N].Def !is null)
            {
                if (!Nont[N].Anonym)
                {
                    NewGenSet(Nont[N].First, Nont[N].OptExp);
                }
                else
                {
                    Sets.Union(Start, Nont[N].First, Nont[N].IniFollow);
                    NewGenSet(Start, Nont[N].OptExp);
                }
                NewGenSetT(Nont[N].First, Nont[N].FirstIndex);
                NewGenSetT(Nont[N].Follow, Nont[N].FollowIndex);
            }
            if (EAG.HNont[N].Def.Sub.Next !is null)
            {
                NewGenSet(Nont[N].First, Nont[N].AltExp);
            }
        }
    }
}

void GenerateMod(bool ParsePass)
{
    IO.TextOut Mod;
    TextIn Fix;
    int N;
    int Tok;
    Sets.OpenSet AllToks;
    char[] Name = new char[EAG.BaseNameLen + 10];
    bool OpenError;
    bool CompileError;
    long TabTimeStamp;

    void TraverseNont(int N, bool FirstNontCall, Sets.OpenSet Poss)
    {
        bool ExactOneToken;
        int TheOneToken;

        void TraverseAlts(EAG.Alt A, bool FirstNontCall, Sets.OpenSet Poss)
        {
            int Tok;
            Sets.OpenSet Toks;
            bool FirstTok;
            bool LoopNeeded;

            void TraverseFactors(EAG.Factor F, bool FirstNontCall, Sets.OpenSet Poss)
            {
                Sets.OpenSet Poss1;
                bool TwoCalls;
                TwoCalls = false;
                Sets.New(Poss1, nToks);
                Sets.Assign(Poss1, Poss);
                while (F !is null)
                {
                    if (cast(EAG.Term) F !is null)
                    {
                        if (Sets.In(Poss1, (cast(EAG.Term) F).Sym - EAG.firstHTerm + firstUserTok))
                        {
                            Sets.Excl(Poss1, (cast(EAG.Term) F).Sym - EAG.firstHTerm + firstUserTok);
                            if (Sets.IsEmpty(Poss1))
                            {
                                IO.WriteText(Mod, "S.Get(Tok); IsRepairMode = false;\n");
                            }
                            else
                            {
                                IO.WriteText(Mod, "if (Tok != ");
                                IO.WriteInt(Mod, (cast(EAG.Term) F).Sym - EAG.firstHTerm + firstUserTok);
                                IO.WriteText(Mod, ")\n");
                                IO.WriteText(Mod, "RecoveryTerminal(");
                                IO.WriteInt(Mod, (cast(EAG.Term) F).Sym - EAG.firstHTerm + firstUserTok);
                                IO.WriteText(Mod, ", ");
                                IO.WriteInt(Mod, Factor[F.Ind].Rec - firstGenSet);
                                IO.WriteText(Mod, ");\n");
                                IO.WriteText(Mod, "else\n");
                                IO.WriteText(Mod, "{\n");
                                IO.WriteText(Mod, "S.Get(Tok); IsRepairMode = false;\n");
                                IO.WriteText(Mod, "}\n");
                            }
                        }
                        else
                        {
                            IO.WriteText(Mod, "RecoveryTerminal(");
                            IO.WriteInt(Mod, (cast(EAG.Term) F).Sym - EAG.firstHTerm + firstUserTok);
                            IO.WriteText(Mod, ", ");
                            IO.WriteInt(Mod, Factor[F.Ind].Rec - firstGenSet);
                            IO.WriteText(Mod, ");\n");
                        }
                        Sets.Assign(Poss1, AllToks);
                    }
                    else
                    {
                        if (Sets.In(GenNonts, (cast(EAG.Nont) F).Sym))
                        {
                            EvalGen.GenSynPred(N, (cast(EAG.Nont) F).Actual.Params);
                            if (!Nont[(cast(EAG.Nont) F).Sym].Anonym)
                            {
                                if (FirstNontCall)
                                {
                                    IO.WriteText(Mod, "if (RecTop >= RecStack.length) ParserExpand;\n");
                                    FirstNontCall = false;
                                }
                                if (TwoCalls)
                                {
                                    IO.WriteText(Mod, "RecStack[RecTop - 1] = ");
                                }
                                else
                                {
                                    IO.WriteText(Mod, "RecStack[RecTop] = ");
                                }
                                IO.WriteInt(Mod, Factor[F.Ind].Rec - firstGenSet);
                                if (TwoCalls)
                                {
                                    IO.WriteText(Mod, ";\n");
                                }
                                else
                                {
                                    IO.WriteText(Mod, "; INC(RecTop);\n");
                                }
                                if (UseReg && !Sets.In(RegNonts, N)
                                        && Sets.In(RegNonts, (cast(EAG.Nont) F).Sym))
                                {
                                    IO.WriteText(Mod, "S.Get = &S.Get3;\n");
                                }
                                IO.WriteText(Mod, "P");
                                IO.WriteInt(Mod, (cast(EAG.Nont) F).Sym);
                                EvalGen.GenActualParams((cast(EAG.Nont) F).Actual.Params, true);
                                IO.WriteText(Mod, ";");
                                IO.WriteText(Mod, " // ");
                                EAG.WriteHNont(Mod, (cast(EAG.Nont) F).Sym);
                                IO.WriteText(Mod, "\n");
                                if (UseReg && !Sets.In(RegNonts, N)
                                        && Sets.In(RegNonts, (cast(EAG.Nont) F).Sym))
                                {
                                    IO.WriteText(Mod, "if (Tok == sepTok)\n");
                                    IO.WriteText(Mod, "{\n");
                                    IO.WriteText(Mod, "S.Get(Tok);\n");
                                    IO.WriteText(Mod, "IsRepairMode = false;\n");
                                    IO.WriteText(Mod, "}\n");
                                    IO.WriteText(Mod, "S.Get = &S.Get2;\n");
                                }
                                if (F.Next !is null && cast(EAG.Nont) F.Next !is null
                                        && Sets.In(GenNonts, (cast(EAG.Nont) F.Next).Sym)
                                        && !Nont[(cast(EAG.Nont) F.Next).Sym].Anonym)
                                {
                                    TwoCalls = true;
                                }
                                else
                                {
                                    TwoCalls = false;
                                }
                                if (!TwoCalls)
                                {
                                    IO.WriteText(Mod, "DEC(RecTop);\n");
                                }
                            }
                            else
                            {
                                TraverseNont((cast(EAG.Nont) F).Sym, FirstNontCall, Poss1);
                            }
                            EvalGen.GenAnalPred(N, (cast(EAG.Nont) F).Actual.Params);
                            Sets.Assign(Poss1, AllToks);
                        }
                        else if (Sets.In(EAG.Pred, (cast(EAG.Nont) F).Sym))
                        {
                            EvalGen.GenSynPred(N, (cast(EAG.Nont) F).Actual.Params);
                            EvalGen.GenPredCall((cast(EAG.Nont) F).Sym, (cast(EAG.Nont) F).Actual.Params);
                            EvalGen.GenAnalPred(N, (cast(EAG.Nont) F).Actual.Params);
                        }
                        else
                        {
                            Warning = true;
                            IO.WriteText(Mod,
                                    "throw new Exception(\"  runtime error: call of nonproductive nonterminal!\");\n");
                            IO.WriteText(IO.Msg, "\n  generated compiler contains corrupt code");
                            IO.WriteText(IO.Msg, "\n    for nonproductive nonterminals!");
                            IO.Update(IO.Msg);
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
                if (cast(EAG.Rep) EAG.HNont[N].Def !is null)
                {
                    EvalGen.GenRepAlt(N, A);
                }
                else
                {
                    EvalGen.GenSynPred(N, A.Formal.Params);
                }
            }
            else
            {
                Sets.New(Toks, nToks);
                if (!Sets.In(EAG.Null, N))
                {
                    Sets.Assign(Toks, Nont[N].First);
                }
                else
                {
                    Sets.Union(Toks, Nont[N].First, Nont[N].Follow);
                }
                if (Sets.Included(Toks, Poss))
                {
                    LoopNeeded = false;
                }
                else
                {
                    LoopNeeded = true;
                }
                if (LoopNeeded)
                {
                    IO.WriteText(Mod, "loop: while (1)\n");
                    IO.WriteText(Mod, "{\n");
                }
                IO.WriteText(Mod, "switch (Tok)\n");
                IO.WriteText(Mod, "{\n");
                do
                {
                    if (!LoopNeeded && Sets.Disjoint(Alt[A.Ind].Dir, Poss))
                    {
                        writeln;
                        writeln(A.Pos);
                        IO.WriteText(IO.Msg, "  dead alternative in ");
                        EAG.WriteNamedHNont(IO.Msg, N);
                        IO.Update(IO.Msg);
                        Warning = true;
                    }
                    IO.WriteText(Mod, "case ");
                    FirstTok = true;
                    for (Tok = 0; Tok <= nToks - 1; ++Tok)
                    {
                        if (Sets.In(Alt[A.Ind].Dir, Tok))
                        {
                            if (!FirstTok)
                            {
                                IO.WriteText(Mod, ":\n");
                                IO.WriteText(Mod, "case ");
                            }
                            IO.WriteInt(Mod, Tok);
                            FirstTok = false;
                        }
                    }
                    IO.WriteText(Mod, ":\n");
                    EvalGen.InitScope(A.Scope);
                    EvalGen.GenAnalPred(N, A.Formal.Params);
                    TraverseFactors(A.Sub, FirstNontCall, Alt[A.Ind].Dir);
                    if (cast(EAG.Rep) EAG.HNont[N].Def !is null)
                    {
                        EvalGen.GenRepAlt(N, A);
                    }
                    else
                    {
                        EvalGen.GenSynPred(N, A.Formal.Params);
                    }
                    if (LoopNeeded)
                    {
                        IO.WriteText(Mod, "break loop;\n");
                    }
                    else
                    {
                        IO.WriteText(Mod, "break;\n");
                    }
                    A = A.Next;
                }
                while (A !is null);
                if (LoopNeeded)
                {
                    A = Nont[N].DefaultAlt;
                    IO.WriteText(Mod, "default:\n");
                    IO.WriteText(Mod, "if (IsRepairMode)\n");
                    IO.WriteText(Mod, "{\n");
                    Sets.Difference(Toks, AllToks, Toks);
                    EvalGen.InitScope(A.Scope);
                    EvalGen.GenAnalPred(N, A.Formal.Params);
                    TraverseFactors(A.Sub, FirstNontCall, Toks);
                    if (cast(EAG.Rep) EAG.HNont[N].Def !is null)
                    {
                        EvalGen.GenRepAlt(N, A);
                    }
                    else
                    {
                        EvalGen.GenSynPred(N, A.Formal.Params);
                    }
                    IO.WriteText(Mod, "break loop;\n");
                    IO.WriteText(Mod, "}\n");
                    IO.WriteText(Mod, "ErrorRecovery(");
                    IO.WriteInt(Mod, Nont[N].AltExp - firstGenSet);
                    IO.WriteText(Mod, ", ");
                    IO.WriteInt(Mod, Nont[N].AltRec - firstGenSet);
                    IO.WriteText(Mod, ");\n");
                }
                else
                {
                    IO.WriteText(Mod, "default: assert(0);\n");
                }
                IO.WriteText(Mod, "}\n");
                if (LoopNeeded)
                {
                    IO.WriteText(Mod, "}\n");
                }
            }
        }

        void TestOneToken(Sets.OpenSet Toks, ref bool ExactOneToken, ref int TheOneToken)
        {
            int Tok;
            Tok = 0;
            ExactOneToken = false;
            while (Tok < nToks)
            {
                if (Sets.In(Toks, Tok))
                {
                    if (ExactOneToken)
                    {
                        ExactOneToken = false;
                        return;
                    }
                    else
                    {
                        ExactOneToken = true;
                        TheOneToken = Tok;
                    }
                }
                ++Tok;
            }
        }

        if (cast(EAG.Opt) EAG.HNont[N].Def !is null)
        {
            if (Sets.Included(Nont[N].Follow, Poss) && Sets.Disjoint(Nont[N].First, Poss))
            {
                writeln;
                writeln(EAG.HNont[N].Def.Sub.Pos);
                IO.WriteText(IO.Msg, "  dead [ ] - brackets in ");
                EAG.WriteNamedHNont(IO.Msg, N);
                IO.Update(IO.Msg);
                Warning = true;
            }
            else if (Sets.Included(Nont[N].First, Poss))
            {
                writeln;
                writeln(EAG.HNont[N].Def.Sub.Pos);
                IO.WriteText(IO.Msg, "  useless [ ] - brackets in ");
                EAG.WriteNamedHNont(IO.Msg, N);
                IO.Update(IO.Msg);
                Warning = true;
            }
            IO.WriteText(Mod, "while (1)\n");
            IO.WriteText(Mod, "{");
            IO.WriteText(Mod, "if (");
            TestOneToken(Nont[N].First, ExactOneToken, TheOneToken);
            if (ExactOneToken)
            {
                IO.WriteText(Mod, "Tok == ");
                IO.WriteInt(Mod, TheOneToken);
            }
            else
            {
                IO.WriteText(Mod, "IN(SetT[");
                IO.WriteInt(Mod, DIV(Nont[N].FirstIndex - firstGenSetT, nElemsPerSET));
                IO.WriteText(Mod, "][Tok], ");
                IO.WriteInt(Mod, MOD(Nont[N].FirstIndex - firstGenSetT, nElemsPerSET));
                IO.WriteText(Mod, ")");
            }
            IO.WriteText(Mod, ")\n");
            IO.WriteText(Mod, "{\n");
            TraverseAlts(EAG.HNont[N].Def.Sub, FirstNontCall, Nont[N].First);
            IO.WriteText(Mod, "break;\n");
            IO.WriteText(Mod, "}\n");
            IO.WriteText(Mod, "else if (");
            TestOneToken(Nont[N].Follow, ExactOneToken, TheOneToken);
            if (ExactOneToken)
            {
                IO.WriteText(Mod, "Tok == ");
                IO.WriteInt(Mod, TheOneToken);
            }
            else
            {
                IO.WriteText(Mod, "IN(SetT[");
                IO.WriteInt(Mod, DIV(Nont[N].FollowIndex - firstGenSetT, nElemsPerSET));
                IO.WriteText(Mod, "][Tok], ");
                IO.WriteInt(Mod, MOD(Nont[N].FollowIndex - firstGenSetT, nElemsPerSET));
                IO.WriteText(Mod, ")");
            }
            IO.WriteText(Mod, " || IsRepairMode)\n");
            IO.WriteText(Mod, "{\n");
            EvalGen.InitScope((cast(EAG.Opt) EAG.HNont[N].Def).Scope);
            EvalGen.GenAnalPred(N, (cast(EAG.Opt) EAG.HNont[N].Def).Formal.Params);
            EvalGen.GenSynPred(N, (cast(EAG.Opt) EAG.HNont[N].Def).Formal.Params);
            IO.WriteText(Mod, "break;\n");
            IO.WriteText(Mod, "}\n");
            IO.WriteText(Mod, "ErrorRecovery(");
            IO.WriteInt(Mod, Nont[N].OptExp - firstGenSet);
            IO.WriteText(Mod, ", ");
            IO.WriteInt(Mod, Nont[N].OptRec - firstGenSet);
            IO.WriteText(Mod, ");\n");
            IO.WriteText(Mod, "}\n");
        }
        else if (cast(EAG.Rep) EAG.HNont[N].Def !is null)
        {
            if (Sets.Included(Nont[N].Follow, Poss) && Sets.Disjoint(Nont[N].First, Poss))
            {
                writeln;
                writeln(EAG.HNont[N].Def.Sub.Pos);
                IO.WriteText(IO.Msg, "  dead { } - braces in ");
                EAG.WriteNamedHNont(IO.Msg, N);
                IO.Update(IO.Msg);
                Warning = true;
            }
            EvalGen.GenRepStart(N);
            IO.WriteText(Mod, "while (1)\n");
            IO.WriteText(Mod, "{\n");
            IO.WriteText(Mod, "if (");
            TestOneToken(Nont[N].First, ExactOneToken, TheOneToken);
            if (ExactOneToken)
            {
                IO.WriteText(Mod, "Tok == ");
                IO.WriteInt(Mod, TheOneToken);
            }
            else
            {
                IO.WriteText(Mod, "IN(SetT[");
                IO.WriteInt(Mod, DIV(Nont[N].FirstIndex - firstGenSetT, nElemsPerSET));
                IO.WriteText(Mod, "][Tok], ");
                IO.WriteInt(Mod, MOD(Nont[N].FirstIndex - firstGenSetT, nElemsPerSET));
                 IO.WriteText(Mod, ")");
           }
            IO.WriteText(Mod, ")\n");
            IO.WriteText(Mod, "{\n");
            TraverseAlts(EAG.HNont[N].Def.Sub, FirstNontCall, Nont[N].First);
            IO.WriteText(Mod, "}\n");
            IO.WriteText(Mod, "else if (");
            TestOneToken(Nont[N].Follow, ExactOneToken, TheOneToken);
            if (ExactOneToken)
            {
                IO.WriteText(Mod, "Tok == ");
                IO.WriteInt(Mod, TheOneToken);
            }
            else
            {
                IO.WriteText(Mod, "IN(SetT[");
                IO.WriteInt(Mod, DIV(Nont[N].FollowIndex - firstGenSetT, nElemsPerSET));
                IO.WriteText(Mod, "][Tok], ");
                IO.WriteInt(Mod, MOD(Nont[N].FollowIndex - firstGenSetT, nElemsPerSET));
                IO.WriteText(Mod, ")");
            }
            IO.WriteText(Mod, " || IsRepairMode) break;\n");
            IO.WriteText(Mod, "else ErrorRecovery(");
            IO.WriteInt(Mod, Nont[N].OptExp - firstGenSet);
            IO.WriteText(Mod, ", ");
            IO.WriteInt(Mod, Nont[N].OptRec - firstGenSet);
            IO.WriteText(Mod, ");\n");
            IO.WriteText(Mod, "}\n");
            EvalGen.GenRepEnd(N);
        }
        else
        {
            TraverseAlts(EAG.HNont[N].Def.Sub, FirstNontCall, Poss);
        }
    }

    void WriteTab(char[] Name)
    {
        const magicNumber = 827092037;
        IO.File Tab;
        int i;
        int j;
        int m;
        int Tok;
        uint s;
        IO.CreateFile(Tab, Name);
        IO.PutLInt(Tab, magicNumber);
        IO.PutLInt(Tab, TabTimeStamp);
        IO.PutLInt(Tab, 31);
        IO.PutSet(Tab, SET(0, 2, 3, 6, 9, 13, 18, 19, 20, 24, 25, 27, 28, 31));
        for (i = firstGenSetT; i <= NextGenSetT - 1; i = i + nElemsPerSET)
        {
            if (nElemsPerSET <= NextGenSetT - i)
            {
                m = nElemsPerSET;
            }
            else
            {
                m = NextGenSetT - i;
            }
            for (Tok = 0; Tok <= nToks - 1; ++Tok)
            {
                s = SET;
                for (j = 0; j <= m - 1; ++j)
                {
                    if (Sets.In(GenSetT[i + j], Tok))
                    {
                        INCL(s, j);
                    }
                }
                IO.PutSet(Tab, s);
            }
        }
        for (i = firstGenSet; i <= NextGenSet - 1; ++i)
        {
            for (j = 0; j <= Sets.nSetsUsed(GenSet[i]) - 1; ++j)
            {
                IO.PutSet(Tab, Sets.ConvertToSET(GenSet[i], j));
            }
        }
        IO.PutLInt(Tab, magicNumber);
        IO.CloseFile(Tab);
    }

    void InclFix(char Term)
    {
        import std.conv : to;
        import std.exception : enforce;

        char c = Fix.front.to!char;

        while (c != Term)
        {
            enforce(c != 0,
                    "error: unexpected end of eELL1Gen.fix.d");

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

    Sets.New(AllToks, nToks);
    Fix = TextIn("fix/eELL1Gen.fix.d");
    IO.CreateModOut(Mod, EAG.BaseName);
    if (ParsePass)
    {
        EvalGen.InitGen(Mod, EvalGen.parsePass);
    }
    else
    {
        EvalGen.InitGen(Mod, EvalGen.onePass);
    }
    InclFix('$');
    IO.WriteText(Mod, EAG.BaseName);
    InclFix('$');
    Append(Name, EAG.BaseName, "Scan");
    IO.WriteText(Mod, Name);
    if (ParsePass)
    {
        IO.WriteText(Mod, ", Eval = ");
        IO.WriteText(Mod, EAG.BaseName);
        IO.WriteText(Mod, "Eval");
    }
    InclFix('$');
    IO.WriteInt(Mod, nToks);
    InclFix('$');
    IO.WriteInt(Mod, Sets.nSetsUsed(AllToks));
    InclFix('$');
    IO.WriteInt(Mod, DIV(NextGenSetT - firstGenSetT - 1, nElemsPerSET) + 1);
    InclFix('$');
    IO.WriteInt(Mod, NextGenSet - firstGenSet);
    InclFix('$');
    EvalGen.GenDeclarations;
    for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
    {
        if (Sets.In(GenNonts, N))
        {
            if (!Nont[N].Anonym)
            {
                IO.WriteText(Mod, "// ");
                IO.WriteText(Mod, "PROCEDURE^ P");
                IO.WriteInt(Mod, N);
                EvalGen.GenFormalParams(N, true);
                IO.WriteText(Mod, ";");
                IO.WriteText(Mod, "   (* ");
                EAG.WriteHNont(Mod, N);
                IO.WriteText(Mod, " *)\n");
            }
        }
    }
    EvalGen.GenPredProcs;
    InclFix('$');
    TabTimeStamp = IO.TimeStamp();
    IO.WriteInt(Mod, TabTimeStamp);
    InclFix('$');
    Sets.Empty(AllToks);
    for (Tok = 0; Tok <= nToks - 1; ++Tok)
    {
        Sets.Incl(AllToks, Tok);
    }
    for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
    {
        if (Sets.In(GenNonts, N))
        {
            if (!Nont[N].Anonym)
            {
                EvalGen.ComputeVarNames(N, true);
                IO.WriteText(Mod, "void P");
                IO.WriteInt(Mod, N);
                EvalGen.GenFormalParams(N, true);
                IO.WriteText(Mod, " // ");
                EAG.WriteHNont(Mod, N);
                IO.WriteText(Mod, "\n");
                IO.WriteText(Mod, "{\n");
                EvalGen.GenVarDecl(N);
                TraverseNont(N, true, AllToks);
                IO.WriteText(Mod, "}\n\n");
            }
        }
    }
    if (!ParsePass)
    {
        EmitGen.GenEmitProc(Mod);
    }
    InclFix('$');
    if (ParsePass)
    {
        IO.WriteText(Mod, "& Eval.EvalInitSucceeds()");
    }
    InclFix('$');
    IO.WriteText(Mod, EAG.BaseName);
    InclFix('$');
    IO.WriteText(Mod, "P");
    IO.WriteInt(Mod, EAG.StartSym);
    InclFix('$');
    if (ParsePass)
    {
        IO.WriteText(Mod,
                "Eval.TraverseSyntaxTree(Heap, PosHeap, ErrorCounter, V1, arityConst);\n");
        IO.WriteText(Mod, "if (IO.IsOption('i'))\n");
        IO.WriteText(Mod, "{\n");
        IO.WriteText(Mod, "IO.WriteText(IO.Msg, \"\\tsyntax tree uses twice \");\n");
        IO.WriteText(Mod, "IO.WriteInt(IO.Msg, NextHeap); IO.WriteLn(IO.Msg); IO.Update(IO.Msg);\n");
        IO.WriteText(Mod, "}");
    }
    else
    {
        IO.WriteText(Mod, "if (ErrorCounter > 0)\n");
        IO.WriteText(Mod, "{\n");
        IO.WriteText(Mod, "IO.WriteText(IO.Msg, \"  \"); IO.WriteInt(IO.Msg, ErrorCounter);\n");
        IO.WriteText(Mod, "IO.WriteText(IO.Msg, \" errors detected\\n\"); IO.Update(IO.Msg);\n");
        IO.WriteText(Mod, "}\n");
        IO.WriteText(Mod, "else\n");
        IO.WriteText(Mod, "{\n");
        EmitGen.GenEmitCall(Mod);
        IO.WriteText(Mod, "}\n");
        EmitGen.GenShowHeap(Mod);
    }
    InclFix('$');
    IO.WriteText(Mod, EAG.BaseName);
    InclFix('$');
    Append(Name, EAG.BaseName, ".Tab");
    IO.WriteText(Mod, Name);
    InclFix('$');
    IO.WriteText(Mod, EAG.BaseName);
    InclFix('$');
    Append(Name, EAG.BaseName, ".Tab");
    WriteTab(Name);
    IO.Update(Mod);
    if (ShowMod)
    {
        IO.Show(Mod);
    }
    else
    {
        IO.Compile(Mod, CompileError);
        Compiled = true;
        if (CompileError)
        {
            IO.Show(Mod);
        }
    }
    IO.CloseOut(Mod);
    EvalGen.FinitGen;
}

void Test()
{
    IO.WriteText(IO.Msg, "ELL(1) testing    ");
    IO.WriteString(IO.Msg, EAG.BaseName);
    IO.Update(IO.Msg);
    if (EAG.Performed(SET(EAG.analysed, EAG.predicates)))
    {
        EXCL(EAG.History, EAG.parsable);
        Init;
        if (GrammarOk())
        {
            ComputeDir;
            if (!(Error || Warning))
            {
                IO.WriteText(IO.Msg, "   ok");
                INCL(EAG.History, EAG.parsable);
            }
        }
        Finit;
    }
    IO.WriteLn(IO.Msg);
    IO.Update(IO.Msg);
}

void Generate()
{
    IO.WriteText(IO.Msg, "ELL(1) writing   ");
    IO.WriteString(IO.Msg, EAG.BaseName);
    IO.WriteText(IO.Msg, "   ");
    IO.Update(IO.Msg);
    Compiled = false;
    if (EAG.Performed(SET(EAG.analysed, EAG.predicates, EAG.isSLEAG)))
    {
        EXCL(EAG.History, EAG.parsable);
        Init;
        if (GrammarOk())
        {
            ComputeDir;
            if (!Error)
            {
                ComputeDefaultAlts;
                ComputeSets;
                GenerateMod(false);
                INCL(EAG.History, EAG.parsable);
            }
        }
        Finit;
    }
    if (!Compiled)
    {
        IO.WriteLn(IO.Msg);
    }
    IO.Update(IO.Msg);
}

void GenerateParser()
{
    IO.WriteText(IO.Msg, "ELL(1) writing parser of ");
    IO.WriteString(IO.Msg, EAG.BaseName);
    IO.WriteText(IO.Msg, "   ");
    IO.Update(IO.Msg);
    Compiled = false;
    if (EAG.Performed(SET(EAG.analysed, EAG.predicates, EAG.hasEvaluator)))
    {
        EXCL(EAG.History, EAG.parsable);
        Init;
        if (GrammarOk())
        {
            EAG.History = SET;
            Shift.Shift(0);
            ComputeDir;
            if (!Error)
            {
                ComputeDefaultAlts;
                ComputeSets;
                GenerateMod(true);
            }
        }
        Finit;
    }
    if (!Compiled)
    {
        IO.WriteLn(IO.Msg);
    }
    IO.Update(IO.Msg);
}

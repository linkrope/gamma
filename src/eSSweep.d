module eSSweep;

import runtime;
import Sets = eSets;
import IO = eIO;
import EAG = eEAG;
import EmitGen = eEmitGen;
import EvalGen = eSLEAGGen;

const nil = 0;
const indexOfFirstAlt = 1;
int[] FactorOffset;
Sets.OpenSet GenNonts;
Sets.OpenSet GenFactors;
bool Error;
bool ShowMod;
bool Compiled;

void Init()
{
    NEW(FactorOffset, EAG.NextHFactor + EAG.NextHAlt + 1);
    Sets.New(GenFactors, EAG.NextHNont);
    Sets.Intersection(GenFactors, EAG.Prod, EAG.Reach);
    Sets.New(GenNonts, EAG.NextHNont);
    Sets.Difference(GenNonts, GenFactors, EAG.Pred);
    Error = false;
    ShowMod = IO.IsOption('m');
}

void Finit()
{
    FactorOffset = null;
}

void GenerateMod(bool CreateMod)
{
    const firstEdge = 1;
    const firstStack = 0;

    struct EdgeRecord
    {
        int Dest;
        int Next;
    }

    alias OpenEdge = EdgeRecord[];

    struct FactorRecord
    {
        int Vars;
        int CountAppl;
        int Prio;
        EAG.Factor F;
    }

    struct VarRecord
    {
        int Factors;
    }

    int N;
    int V;
    IO.TextOut Mod;
    IO.TextIn Fix;
    char[] Name = new char[EAG.BaseNameLen + 10];
    bool OpenError;
    bool CompileError;
    EAG.Rule SavedNontDef;
    int SavedNextHFactor;
    int SavedNextHAlt;
    FactorRecord[] Factor;
    VarRecord[] Var;
    OpenEdge Edge;
    int NextEdge;
    int[] Stack;
    int NextStack;
    Sets.OpenSet DefVars;

    void Expand()
    {
        OpenEdge Edge1;
        long i;
        if (NextEdge >= Edge.length)
        {
            NEW(Edge1, 2 * Edge.length);
            for (i = firstEdge; i <= Edge.length - 1; ++i)
            {
                Edge1[i] = Edge[i];
            }
            Edge = Edge1;
        }
    }

    void InclFix(char Term)
    {
        char c;
        IO.Read(Fix, c);
        while (c != Term)
        {
            if (c == '\x00')
            {
                IO.WriteText(IO.Msg, "\n  error: unexpected end of eSSweep.Fix\n");
                IO.Update(IO.Msg);
                HALT(99);
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

    int HyperArity()
    {
        int N;
        int i;
        int Max;
        EAG.Alt A;
        Sets.OpenSet Nonts;
        Sets.New(Nonts, EAG.NextHNont);
        Sets.Difference(Nonts, EAG.All, EAG.Pred);
        Max = 0;
        for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
        {
            if (Sets.In(Nonts, N))
            {
                A = EAG.HNont[N].Def.Sub;
                i = 0;
                do
                {
                    ++i;
                    A = A.Next;
                }
                while (A !is null);
                if (cast(EAG.Opt) EAG.HNont[N].Def !is null || cast(EAG.Rep) EAG.HNont[N].Def !is null)
                {
                    ++i;
                }
                if (i > Max)
                {
                    Max = i;
                }
            }
        }
        i = 1;
        while (i <= Max)
        {
            i = i * 2;
        }
        return i;
    }

    void SaveAndPatchNont(int N)
    {
        EAG.Grp Def;
        EAG.Alt A;
        EAG.Alt A1;
        EAG.Alt A2;
        EAG.Factor F;
        EAG.Nont F1;
        EAG.Nont F2;
        SavedNontDef = EAG.HNont[N].Def;
        SavedNextHFactor = EAG.NextHFactor;
        SavedNextHAlt = EAG.NextHAlt;
        NEW(Def);
        A = EAG.HNont[N].Def.Sub;
        A2 = null;
        do
        {
            NEW(A1);
            A1 = A;
            A1.Sub = null;
            A1.Last = null;
            A1.Next = null;
            if (A2 !is null)
            {
                A2.Next = A1;
            }
            else
            {
                Def.Sub = A1;
            }
            A2 = A1;
            F = A.Sub;
            F2 = null;
            while (F !is null)
            {
                if (cast(EAG.Nont) F !is null && Sets.In(GenFactors, (cast(EAG.Nont) F).Sym))
                {
                    NEW(F1);
                    F1 = (cast(EAG.Nont) F);
                    F1.Prev = F2;
                    F1.Next = null;
                    A1.Last = F1;
                    if (F2 !is null)
                    {
                        F2.Next = F1;
                    }
                    else
                    {
                        A1.Sub = F1;
                    }
                    F2 = F1;
                }
                F = F.Next;
            }
            if (cast(EAG.Rep) EAG.HNont[N].Def !is null)
            {
                NEW(F1);
                F1.Ind = EAG.NextHFactor;
                ++EAG.NextHFactor;
                F1.Prev = A1.Last;
                A1.Last = F1;
                if (A1.Sub is null)
                {
                    A1.Sub = F1;
                }
                if (F1.Prev !is null)
                {
                    F1.Prev.Next = F1;
                }
                F1.Next = null;
                F1.Sym = N;
                F1.Pos = A1.Actual.Pos;
                F1.Actual = A1.Actual;
                A1.Actual.Pos = IO.UndefPos;
                A1.Actual.Params = EAG.empty;
            }
            A = A.Next;
        }
        while (A !is null);
        if (cast(EAG.Opt) EAG.HNont[N].Def !is null || cast(EAG.Rep) EAG.HNont[N].Def !is null)
        {
            NEW(A1);
            A1.Ind = EAG.NextHAlt;
            ++EAG.NextHAlt;
            A1.Up = N;
            A1.Next = null;
            A1.Sub = null;
            A1.Last = null;
            if (cast(EAG.Opt) EAG.HNont[N].Def !is null)
            {
                A1.Scope = (cast(EAG.Opt) EAG.HNont[N].Def).Scope;
                A1.Formal = (cast(EAG.Opt) EAG.HNont[N].Def).Formal;
                A1.Pos = (cast(EAG.Opt) EAG.HNont[N].Def).EmptyAltPos;
            }
            else
            {
                A1.Scope = (cast(EAG.Rep) EAG.HNont[N].Def).Scope;
                A1.Formal = (cast(EAG.Rep) EAG.HNont[N].Def).Formal;
                A1.Pos = (cast(EAG.Rep) EAG.HNont[N].Def).EmptyAltPos;
            }
            A1.Actual.Params = EAG.empty;
            A1.Actual.Pos = IO.UndefPos;
            A2.Next = A1;
        }
        EAG.HNont[N].Def = Def;
    }

    void RestoreNont(int N)
    {
        EAG.HNont[N].Def = SavedNontDef;
        EAG.NextHFactor = SavedNextHFactor;
        EAG.NextHAlt = SavedNextHAlt;
    }

    void ComputePermutation(int N)
    {
        const def = 0;
        const right = 1;
        const appl = 2;
        EAG.Alt A;
        EAG.Factor F;
        EAG.Factor F1;
        int Prio;
        int Index;
        int Offset;
        int NE;
        int VE;
        int V;

        void TravParams(int op, int P, EAG.Factor F)
        {
            bool Def;

            void NewEdge(ref int From, int To)
            {
                if (NextEdge >= Edge.length)
                {
                    Expand;
                }
                Edge[NextEdge].Dest = To;
                Edge[NextEdge].Next = From;
                From = NextEdge;
                ++NextEdge;
            }

            void Tree(int Node)
            {
                int n;
                if (Node < 0)
                {
                    switch (op)
                    {
                    case def:
                        if (Def)
                        {
                            Sets.Incl(DefVars, -Node);
                        }
                        break;
                    case right:
                        if (!Sets.In(DefVars, -Node))
                        {
                            if (Def)
                            {
                                NewEdge(Factor[F.Ind].Vars, -Node);
                            }
                            else
                            {
                                NewEdge(Var[-Node].Factors, F.Ind);
                                ++Factor[F.Ind].CountAppl;
                            }
                        }
                        break;
                    case appl:
                        if (!Def && !Sets.In(DefVars, -Node))
                        {
                            IO.WriteText(IO.Msg, "\n  ");
                            IO.WritePos(IO.Msg, EAG.ParamBuf[P].Pos);
                            IO.WriteText(IO.Msg, "  variable '");
                            EAG.WriteVar(IO.Msg, -Node);
                            IO.WriteText(IO.Msg, "' is not defined");
                            IO.Update(IO.Msg);
                            Error = true;
                        }
                        break;
                    default:
                        assert(0);
                    }
                }
                else
                {
                    for (n = 1; n <= EAG.MAlt[EAG.NodeBuf[Node]].Arity; ++n)
                    {
                        Tree(EAG.NodeBuf[Node + n]);
                    }
                }
            }

            while (EAG.ParamBuf[P].Affixform != EAG.nil)
            {
                Def = EAG.ParamBuf[P].isDef;
                Tree(EAG.ParamBuf[P].Affixform);
                ++P;
            }
        }

        void Pop(ref EAG.Factor F)
        {
            int i;
            int MinPrio;
            int MinIndex;
            MinPrio = int.max;
            for (i = firstStack; i <= NextStack - 1; ++i)
            {
                if (Factor[Stack[i]].Prio < MinPrio)
                {
                    MinPrio = Factor[Stack[i]].Prio;
                    MinIndex = i;
                }
            }
            F = Factor[Stack[MinIndex]].F;
            Stack[MinIndex] = Stack[NextStack - 1];
            --NextStack;
        }

        A = EAG.HNont[N].Def.Sub;
        do
        {
            Sets.Empty(DefVars);
            NextEdge = firstEdge;
            NextStack = firstStack;
            TravParams(def, A.Formal.Params, null);
            F = A.Sub;
            Prio = 0;
            Offset = 1;
            while (F !is null)
            {
                Factor[F.Ind].Vars = nil;
                Factor[F.Ind].CountAppl = 0;
                Factor[F.Ind].Prio = Prio;
                ++Prio;
                Factor[F.Ind].F = F;
                if (!Sets.In(EAG.Pred, (cast(EAG.Nont) F).Sym))
                {
                    FactorOffset[F.Ind] = Offset;
                    ++Offset;
                }
                TravParams(right, (cast(EAG.Nont) F).Actual.Params, F);
                if (Factor[F.Ind].CountAppl == 0)
                {
                    Stack[NextStack] = F.Ind;
                    ++NextStack;
                }
                F = F.Next;
            }
            A.Sub = null;
            A.Last = null;
            F1 = null;
            Index = 0;
            while (NextStack > firstStack)
            {
                Pop(F);
                F.Prev = F1;
                F.Next = null;
                A.Last = F;
                if (F1 !is null)
                {
                    F1.Next = F;
                }
                else
                {
                    A.Sub = F;
                }
                F1 = F;
                ++Index;
                VE = Factor[F.Ind].Vars;
                while (VE != nil)
                {
                    V = Edge[VE].Dest;
                    if (!Sets.In(DefVars, V))
                    {
                        NE = Var[V].Factors;
                        while (NE != nil)
                        {
                            --Factor[Edge[NE].Dest].CountAppl;
                            if (Factor[Edge[NE].Dest].CountAppl == 0)
                            {
                                Stack[NextStack] = Edge[NE].Dest;
                                ++NextStack;
                            }
                            NE = Edge[NE].Next;
                        }
                        Sets.Incl(DefVars, V);
                    }
                    VE = Edge[VE].Next;
                }
            }
            if (Index == Prio)
            {
                TravParams(appl, A.Formal.Params, null);
            }
            else
            {
                IO.WriteText(IO.Msg, "\n  ");
                IO.WritePos(IO.Msg, A.Pos);
                IO.WriteText(IO.Msg, "  alternative is not single sweep");
                IO.Update(IO.Msg);
                Error = true;
            }
            A = A.Next;
        }
        while (A !is null);
    }

    void GenerateNont(int N)
    {
        EAG.Alt A;
        EAG.Factor F;
        EAG.Factor F1;
        int AltIndex;
        EvalGen.ComputeVarNames(N, false);
        IO.WriteText(Mod, "PROCEDURE P");
        IO.WriteInt(Mod, N);
        IO.WriteText(Mod, "(Adr : TreeType");
        EvalGen.GenFormalParams(N, false);
        IO.WriteText(Mod, ");");
        IO.WriteText(Mod, "   (* ");
        EAG.WriteHNont(Mod, N);
        if (EAG.HNont[N].Id < 0)
        {
            IO.WriteText(Mod, " in ");
            EAG.WriteNamedHNont(Mod, N);
        }
        IO.WriteText(Mod, " *)\n");
        EvalGen.GenVarDecl(N);
        IO.WriteText(Mod, "BEGIN\n");
        IO.WriteText(Mod, "\tCASE Tree[Adr] MOD hyperArityConst OF\n");
        A = EAG.HNont[N].Def.Sub;
        AltIndex = indexOfFirstAlt;
        do
        {
            IO.WriteText(Mod, "\t\t| ");
            IO.WriteInt(Mod, AltIndex);
            IO.WriteText(Mod, " : \n");
            EvalGen.InitScope(A.Scope);
            if (EvalGen.PosNeeded(A.Formal.Params))
            {
                IO.WriteText(Mod, "Pos := PosTree[Adr];\n");
            }
            EvalGen.GenAnalPred(N, A.Formal.Params);
            F = A.Sub;
            while (F !is null)
            {
                if (!Sets.In(EAG.Pred, (cast(EAG.Nont) F).Sym))
                {
                    EvalGen.GenSynPred(N, (cast(EAG.Nont) F).Actual.Params);
                    IO.WriteText(Mod, "\t\tP");
                    IO.WriteInt(Mod, (cast(EAG.Nont) F).Sym);
                    IO.WriteText(Mod, "(Tree[Adr + ");
                    IO.WriteInt(Mod, FactorOffset[F.Ind]);
                    IO.WriteText(Mod, "]");
                    EvalGen.GenActualParams((cast(EAG.Nont) F).Actual.Params, false);
                    IO.WriteText(Mod, ");   (* ");
                    EAG.WriteHNont(Mod, (cast(EAG.Nont) F).Sym);
                    if (EAG.HNont[(cast(EAG.Nont) F).Sym].Id < 0)
                    {
                        IO.WriteText(Mod, " in ");
                        EAG.WriteNamedHNont(Mod, (cast(EAG.Nont) F).Sym);
                    }
                    IO.WriteText(Mod, " *)\n");
                    if (EvalGen.PosNeeded((cast(EAG.Nont) F).Actual.Params))
                    {
                        IO.WriteText(Mod, "Pos := PosTree[Adr + ");
                        IO.WriteInt(Mod, FactorOffset[F.Ind]);
                        IO.WriteText(Mod, "];\n");
                    }
                    EvalGen.GenAnalPred(N, (cast(EAG.Nont) F).Actual.Params);
                }
                else
                {
                    EvalGen.GenSynPred(N, (cast(EAG.Nont) F).Actual.Params);
                    IO.WriteText(Mod, "Pos := PosTree[Adr + ");
                    F1 = F.Prev;
                    while (F1 !is null && Sets.In(EAG.Pred, (cast(EAG.Nont) F1).Sym))
                    {
                        F1 = F1.Prev;
                    }
                    if (F1 is null)
                    {
                        IO.WriteInt(Mod, 0);
                    }
                    else
                    {
                        IO.WriteInt(Mod, FactorOffset[F1.Ind]);
                    }
                    IO.WriteText(Mod, "];\n");
                    EvalGen.GenPredCall((cast(EAG.Nont) F).Sym, (cast(EAG.Nont) F).Actual.Params);
                    EvalGen.GenAnalPred(N, (cast(EAG.Nont) F).Actual.Params);
                }
                F = F.Next;
            }
            EvalGen.GenSynPred(N, A.Formal.Params);
            A = A.Next;
            ++AltIndex;
        }
        while (A !is null);
        IO.WriteText(Mod, "\tEND;\n");
        IO.WriteText(Mod, "END P");
        IO.WriteInt(Mod, N);
        IO.WriteText(Mod, ";\n\n");
    }

    EvalGen.InitTest;
    Error = Error || !EvalGen.PredsOK();
    if (CreateMod)
    {
        IO.OpenIn(Fix, "eSSweep.Fix", OpenError);
        if (OpenError)
        {
            IO.WriteText(IO.Msg, "\n  error: could not open eSSweep.Fix\n");
            IO.Update(IO.Msg);
            HALT(99);
        }
        Append(Name, EAG.BaseName, "Eval");
        IO.CreateModOut(Mod, Name);
        if (!Error)
        {
            EvalGen.InitGen(Mod, EvalGen.sSweepPass);
            InclFix('$');
            IO.WriteText(Mod, Name);
            InclFix('$');
            IO.WriteInt(Mod, HyperArity());
            InclFix('$');
            EvalGen.GenDeclarations;
            for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
            {
                if (Sets.In(GenNonts, N))
                {
                    IO.WriteText(Mod, "PROCEDURE^ P");
                    IO.WriteInt(Mod, N);
                    IO.WriteText(Mod, "(Adr : TreeType");
                    EvalGen.GenFormalParams(N, false);
                    IO.WriteText(Mod, ");");
                    IO.WriteText(Mod, "   (* ");
                    EAG.WriteHNont(Mod, N);
                    if (EAG.HNont[N].Id < 0)
                    {
                        IO.WriteText(Mod, " in ");
                        EAG.WriteNamedHNont(Mod, N);
                    }
                    IO.WriteText(Mod, " *)\n");
                }
            }
            EvalGen.GenPredProcs;
            IO.WriteLn(Mod);
        }
    }
    NEW(Factor, EAG.NextHFactor + EAG.NextHAlt + 1);
    NEW(Var, EAG.NextVar + 1);
    NEW(Edge, 127);
    NEW(Stack, EAG.NextHFactor + 1);
    Sets.New(DefVars, EAG.NextVar);
    for (V = EAG.firstVar; V <= EAG.NextVar - 1; ++V)
    {
        Var[V].Factors = nil;
    }
    for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
    {
        if (Sets.In(GenNonts, N))
        {
            SaveAndPatchNont(N);
            ComputePermutation(N);
            if (!Error)
            {
                Error = !EvalGen.IsLEAG(N, true);
                if (!Error && CreateMod)
                {
                    GenerateNont(N);
                }
            }
            RestoreNont(N);
        }
    }
    if (CreateMod)
    {
        if (!Error)
        {
            EmitGen.GenEmitProc(Mod);
            InclFix('$');
            IO.WriteText(Mod, "P");
            IO.WriteInt(Mod, EAG.StartSym);
            InclFix('$');
            EmitGen.GenEmitCall(Mod);
            InclFix('$');
            EmitGen.GenShowHeap(Mod);
            InclFix('$');
            IO.WriteText(Mod, EAG.BaseName);
            IO.WriteText(Mod, "Eval");
            InclFix('$');
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
        }
        EvalGen.FinitGen;
        IO.CloseIn(Fix);
        IO.CloseOut(Mod);
    }
    EvalGen.FinitTest;
}

void Test()
{
    uint SaveHistory;
    IO.WriteText(IO.Msg, "SSweep testing ");
    IO.WriteString(IO.Msg, EAG.BaseName);
    IO.WriteText(IO.Msg, "   ");
    IO.Update(IO.Msg);
    if (EAG.Performed(SET(1 << EAG.analysed | 1 << EAG.predicates)))
    {
        EXCL(EAG.History, EAG.isSSweep);
        Init;
        SaveHistory = EAG.History;
        EAG.History = SET(0);
        GenerateMod(false);
        EAG.History = SaveHistory;
        if (!Error)
        {
            IO.WriteText(IO.Msg, "ok");
            INCL(EAG.History, EAG.isSSweep);
        }
        Finit;
    }
    IO.WriteLn(IO.Msg);
    IO.Update(IO.Msg);
}

void Generate()
{
    uint SaveHistory;
    IO.WriteText(IO.Msg, "SSweep writing ");
    IO.WriteString(IO.Msg, EAG.BaseName);
    IO.WriteText(IO.Msg, "   ");
    IO.Update(IO.Msg);
    Compiled = false;
    if (EAG.Performed(SET(1 << EAG.analysed | 1 << EAG.predicates)))
    {
        EXCL(EAG.History, EAG.isSSweep);
        Init;
        SaveHistory = EAG.History;
        EAG.History = SET(0);
        GenerateMod(true);
        EAG.History = SaveHistory;
        if (!Error)
        {
            INCL(EAG.History, EAG.isSSweep);
            INCL(EAG.History, EAG.hasEvaluator);
        }
        Finit;
    }
    if (!Compiled)
    {
        IO.WriteLn(IO.Msg);
    }
    IO.Update(IO.Msg);
}

module epsilon.ssweep;

import EAG = epsilon.eag;
import EmitGen = epsilon.emitgen;
import IO = epsilon.io;
import EvalGen = epsilon.sleaggen;
import epsilon.settings;
import io : Input, read, UndefPos;
import log;
import runtime;
import std.bitmanip : BitArray;
import std.stdio;
import std.typecons;

private const nil = 0;
private const indexOfFirstAlt = 1;
private int[] FactorOffset;
private BitArray GenNonts;
private BitArray GenFactors;
private bool Error;

public void Test(Settings settings)
in (EAG.Performed(EAG.analysed | EAG.predicates))
{
    info!"single-sweep testing %s"(EAG.BaseName);
    EAG.History &= ~EAG.isSSweep;
    Init;
    scope (exit)
        Finit;

    const SaveHistory = EAG.History;

    EAG.History = 0;
    GenerateMod(No.createMod, settings);
    EAG.History = SaveHistory;
    if (!Error)
    {
        info!"OK";
        EAG.History |= EAG.isSSweep;
    }
}

public void Generate(Settings settings)
in (EAG.Performed(EAG.analysed | EAG.predicates))
{
    info!"single-sweep writing %s"(EAG.BaseName);
    EAG.History &= ~EAG.isSSweep;
    Init;
    scope (exit)
        Finit;

    const SaveHistory = EAG.History;

    EAG.History = 0;
    GenerateMod(Yes.createMod, settings);
    EAG.History = SaveHistory;
    if (!Error)
    {
        EAG.History |= EAG.isSSweep;
        EAG.History |= EAG.hasEvaluator;
    }
}

private void Init() nothrow
{
    FactorOffset = new int[EAG.NextHFactor + EAG.NextHAlt + 1];
    GenFactors = EAG.Prod & EAG.Reach;
    GenNonts = GenFactors - EAG.Pred;
    Error = false;
}

private void Finit() @nogc nothrow @safe
{
    FactorOffset = null;
}

private void GenerateMod(Flag!"createMod" createMod, Settings settings)
{
    const firstEdge = 1;
    const firstStack = 0;

    struct EdgeRecord
    {
        int Dest;
        int Next;
    }

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

    int V;
    IO.TextOut Mod;
    Input Fix;
    string name;
    EAG.Rule SavedNontDef;
    int SavedNextHFactor;
    int SavedNextHAlt;
    FactorRecord[] Factor;
    VarRecord[] Var;
    EdgeRecord[] Edge;
    int NextEdge;
    int[] Stack;
    int NextStack;
    BitArray DefVars;

    void Expand()
    {
        if (NextEdge >= Edge.length)
        {
            auto Edge1 = new EdgeRecord[2 * Edge.length];

            for (size_t i = firstEdge; i < Edge.length; ++i)
            {
                Edge1[i] = Edge[i];
            }
            Edge = Edge1;
        }
    }

    void InclFix(char Term)
    {
        import std.conv : to;
        import std.exception : enforce;

        char c = Fix.front.to!char;

        while (c != Term)
        {
            enforce(c != 0,
                    "error: unexpected end of eSSweep.fix.d");

            Mod.write(c);
            Fix.popFront;
            c = Fix.front.to!char;
        }
        Fix.popFront;
    }

    int HyperArity()
    {
        const Nonts = EAG.All - EAG.Pred;
        int Max = 0;
        int i;

        foreach (N; Nonts.bitsSet)
        {
            EAG.Alt A = EAG.HNont[N].Def.Sub;

            i = 0;
            do
            {
                ++i;
                A = A.Next;
            }
            while (A !is null);
            if (cast(EAG.Opt) EAG.HNont[N].Def !is null || cast(EAG.Rep) EAG.HNont[N].Def !is null)
                ++i;
            if (i > Max)
                Max = i;
        }
        i = 1;
        while (i <= Max)
            i = i * 2;
        return i;
    }

    void SaveAndPatchNont(size_t N)
    {
        import std.conv : to;

        EAG.Alt A;
        EAG.Alt A1;
        EAG.Alt A2;
        EAG.Factor F;
        EAG.Nont F1;
        EAG.Nont F2;

        SavedNontDef = EAG.HNont[N].Def;
        SavedNextHFactor = EAG.NextHFactor;
        SavedNextHAlt = EAG.NextHAlt;

        EAG.Grp Def = new EAG.Grp;

        A = EAG.HNont[N].Def.Sub;
        A2 = null;
        do
        {
            A1 = new EAG.Alt;
            EAG.assign(A1, A);
            A1.Sub = null;
            A1.Last = null;
            A1.Next = null;
            if (A2 !is null)
                A2.Next = A1;
            else
                Def.Sub = A1;
            A2 = A1;
            F = A.Sub;
            F2 = null;
            while (F !is null)
            {
                if (cast(EAG.Nont) F !is null && GenFactors[(cast(EAG.Nont) F).Sym])
                {
                    F1 = new EAG.Nont;
                    EAG.assign(F1, cast(EAG.Nont) F);
                    F1.Prev = F2;
                    F1.Next = null;
                    A1.Last = F1;
                    if (F2 !is null)
                        F2.Next = F1;
                    else
                        A1.Sub = F1;
                    F2 = F1;
                }
                F = F.Next;
            }
            if (cast(EAG.Rep) EAG.HNont[N].Def !is null)
            {
                F1 = new EAG.Nont;
                F1.Ind = EAG.NextHFactor;
                ++EAG.NextHFactor;
                F1.Prev = A1.Last;
                A1.Last = F1;
                if (A1.Sub is null)
                    A1.Sub = F1;
                if (F1.Prev !is null)
                    F1.Prev.Next = F1;
                F1.Next = null;
                F1.Sym = N.to!int;
                F1.Pos = A1.Actual.Pos;
                F1.Actual = A1.Actual;
                A1.Actual.Pos = UndefPos;
                A1.Actual.Params = EAG.empty;
            }
            A = A.Next;
        }
        while (A !is null);
        if (cast(EAG.Opt) EAG.HNont[N].Def !is null || cast(EAG.Rep) EAG.HNont[N].Def !is null)
        {
            A1 = new EAG.Alt;
            A1.Ind = EAG.NextHAlt;
            ++EAG.NextHAlt;
            A1.Up = N.to!int;
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
            A1.Actual.Pos = UndefPos;
            A2.Next = A1;
        }
        EAG.HNont[N].Def = Def;
    }

    void RestoreNont(size_t N)
    {
        EAG.HNont[N].Def = SavedNontDef;
        EAG.NextHFactor = SavedNextHFactor;
        EAG.NextHAlt = SavedNextHAlt;
    }

    void ComputePermutation(size_t N)
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
                            DefVars[-Node] = true;
                        break;
                    case right:
                        if (!DefVars[-Node])
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
                        if (!Def && !DefVars[-Node])
                        {
                            error!"variable %s is not defined\n%s"(EAG.VarRepr(-Node), EAG.ParamBuf[P].Pos);
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
                        Tree(EAG.NodeBuf[Node + n]);
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
            for (i = firstStack; i < NextStack; ++i)
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
            DefVars[] = false;
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
                if (!EAG.Pred[(cast(EAG.Nont) F).Sym])
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
                    F1.Next = F;
                else
                    A.Sub = F;
                F1 = F;
                ++Index;
                VE = Factor[F.Ind].Vars;
                while (VE != nil)
                {
                    V = Edge[VE].Dest;
                    if (!DefVars[V])
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
                        DefVars[V] = true;
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
                error!"alternative is not single sweep\n%s"(A.Pos);
                Error = true;
            }
            A = A.Next;
        }
        while (A !is null);
    }

    void GenerateNont(size_t N)
    {
        EAG.Alt A;
        EAG.Factor F;
        EAG.Factor F1;
        int AltIndex;
        EvalGen.ComputeVarNames(N, No.embed);
        Mod.write("void P");
        Mod.write(N);
        Mod.write("(TreeType Adr");
        EvalGen.GenFormalParams(N, No.parNeeded);
        Mod.write(")");
        Mod.write(" // ");
        Mod.write(EAG.HNontRepr(N));
        if (EAG.HNont[N].anonymous)
        {
            Mod.write(" in ");
            Mod.write(EAG.NamedHNontRepr(N));
        }
        Mod.write("\n");
        Mod.write("{\n");
        EvalGen.GenVarDecl(N);
        Mod.write("switch (MOD(Tree[Adr], hyperArityConst))\n");
        Mod.write("{\n");
        A = EAG.HNont[N].Def.Sub;
        AltIndex = indexOfFirstAlt;
        do
        {
            Mod.write("case ");
            Mod.write(AltIndex);
            Mod.write(":\n");
            EvalGen.InitScope(A.Scope);
            if (EvalGen.PosNeeded(A.Formal.Params))
            {
                Mod.write("Pos = PosTree[Adr];\n");
            }
            EvalGen.GenAnalPred(N, A.Formal.Params);
            F = A.Sub;
            while (F !is null)
            {
                if (!EAG.Pred[(cast(EAG.Nont) F).Sym])
                {
                    EvalGen.GenSynPred(N, (cast(EAG.Nont) F).Actual.Params);
                    Mod.write("P");
                    Mod.write((cast(EAG.Nont) F).Sym);
                    Mod.write("(Tree[Adr + ");
                    Mod.write(FactorOffset[F.Ind]);
                    Mod.write("]");
                    EvalGen.GenActualParams((cast(EAG.Nont) F).Actual.Params, false);
                    Mod.write("); // ");
                    Mod.write(EAG.HNontRepr((cast(EAG.Nont) F).Sym));
                    if (EAG.HNont[(cast(EAG.Nont) F).Sym].anonymous)
                    {
                        Mod.write(" in ");
                        Mod.write(EAG.NamedHNontRepr((cast(EAG.Nont) F).Sym));
                    }
                    Mod.write("\n");
                    if (EvalGen.PosNeeded((cast(EAG.Nont) F).Actual.Params))
                    {
                        Mod.write("Pos = PosTree[Adr + ");
                        Mod.write(FactorOffset[F.Ind]);
                        Mod.write("];\n");
                    }
                    EvalGen.GenAnalPred(N, (cast(EAG.Nont) F).Actual.Params);
                }
                else
                {
                    EvalGen.GenSynPred(N, (cast(EAG.Nont) F).Actual.Params);
                    Mod.write("Pos = PosTree[Adr + ");
                    F1 = F.Prev;
                    while (F1 !is null && EAG.Pred[(cast(EAG.Nont) F1).Sym])
                        F1 = F1.Prev;
                    if (F1 is null)
                        Mod.write(0L);
                    else
                        Mod.write(FactorOffset[F1.Ind]);
                    Mod.write("];\n");
                    EvalGen.GenPredCall((cast(EAG.Nont) F).Sym, (cast(EAG.Nont) F).Actual.Params);
                    EvalGen.GenAnalPred(N, (cast(EAG.Nont) F).Actual.Params);
                }
                F = F.Next;
            }
            EvalGen.GenSynPred(N, A.Formal.Params);
            Mod.write("break;\n");
            A = A.Next;
            ++AltIndex;
        }
        while (A !is null);
        Mod.write("default: assert(0);\n");
        Mod.write("}\n");
        Mod.write("}\n\n");
    }

    EvalGen.InitTest;
    Error = Error || !EvalGen.PredsOK();
    if (createMod)
    {
        Fix = read("fix/epsilon/ssweep.fix.d");
        name = EAG.BaseName ~ "Eval";
        Mod = new IO.TextOut(settings.path(name ~ ".d"));
        if (!Error)
        {
            EvalGen.InitGen(Mod, EvalGen.sSweepPass, settings);
            InclFix('$');
            Mod.write(name);
            InclFix('$');
            Mod.write(HyperArity());
            InclFix('$');
            EvalGen.GenDeclarations(settings);
            EvalGen.GenPredProcs;
            Mod.writeln;
        }
    }
    Factor = new FactorRecord[EAG.NextHFactor + EAG.NextHAlt + 1];
    Var = new VarRecord[EAG.NextVar + 1];
    Edge = new EdgeRecord[127];
    Stack = new int[EAG.NextHFactor + 1];
    DefVars = BitArray();
    DefVars.length = EAG.NextVar + 1;
    for (V = EAG.firstVar; V < EAG.NextVar; ++V)
        Var[V].Factors = nil;
    foreach (N; GenNonts.bitsSet)
    {
        SaveAndPatchNont(N);
        ComputePermutation(N);
        if (!Error)
        {
            Error = !EvalGen.IsLEAG(N, true);
            if (!Error && createMod)
                GenerateNont(N);
        }
        RestoreNont(N);
    }
    if (createMod)
    {
        if (!Error)
        {
            EmitGen.GenEmitProc(Mod, settings);
            InclFix('$');
            Mod.write("P");
            Mod.write(EAG.StartSym);
            InclFix('$');
            EmitGen.GenEmitCall(Mod, settings);
            InclFix('$');
            EmitGen.GenShowHeap(Mod);
            InclFix('$');
            Mod.write(EAG.BaseName);
            Mod.write("Eval");
            InclFix('$');
            Mod.flush;
            if (settings.showMod)
                IO.Show(Mod);
            else
                IO.Compile(Mod);
        }
        EvalGen.FinitGen;
        IO.CloseOut(Mod);
    }
    EvalGen.FinitTest;
}

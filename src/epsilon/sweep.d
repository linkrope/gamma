module epsilon.sweep;

import epsilon.eag;
import EmitGen = epsilon.emitgen;
import epsilon.settings;
import EvalGen = epsilon.slaggen;
import io : Input, read, UndefPos;
import log;
import runtime;
import std.bitmanip : BitArray;
import std.typecons;

private const nil = 0;
private const indexOfFirstAlt = 1;
private int[] FactorOffset;
private int[] predicatePositionOffset;
private BitArray GenNonts;
private BitArray GenFactors;
private bool Error;

public bool Test(Settings settings)
{
    info!"single-sweep testing %s"(eag.BaseName);

    Init;
    scope (exit)
        Finit;

    GenerateMod(No.createMod, settings);
    if (Error)
        return false;

    info!"%s grammar is single sweep"(eag.BaseName);
    return true;
}

public string Generate(Settings settings)
{
    info!"single-sweep writing %s"(eag.BaseName);
    Init;
    scope (exit)
        Finit;

    const fileName = GenerateMod(Yes.createMod, settings);

    return fileName;
}

private void Init() nothrow
{
    FactorOffset = new int[eag.NextHFactor + eag.NextHAlt + 1];
    predicatePositionOffset = new int[FactorOffset.length];
    GenFactors = eag.Prod & eag.Reach;
    GenNonts = GenFactors - eag.Pred;
    Error = false;
}

private void Finit() @nogc nothrow @safe
{
    FactorOffset = null;
    predicatePositionOffset = null;
}

private string GenerateMod(Flag!"createMod" createMod, Settings settings)
{
    import std.stdio : File;

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
    File output;
    Input Fix;
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

            output.write(c);
            Fix.popFront;
            c = Fix.front.to!char;
        }
        Fix.popFront;
    }

    int HyperArity()
    {
        const Nonts = eag.All - eag.Pred;
        int Max = 0;
        int i;

        foreach (N; Nonts.bitsSet)
        {
            EAG.Alt A = eag.HNont[N].Def.Sub;

            i = 0;
            do
            {
                ++i;
                A = A.Next;
            }
            while (A !is null);
            if (cast(EAG.Opt) eag.HNont[N].Def || cast(EAG.Rep) eag.HNont[N].Def)
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

        SavedNontDef = eag.HNont[N].Def;
        SavedNextHFactor = eag.NextHFactor;
        SavedNextHAlt = eag.NextHAlt;

        EAG.Grp Def = new EAG.Grp;

        A = eag.HNont[N].Def.Sub;
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
                if (auto nont = cast(EAG.Nont) F)
                    if (GenFactors[nont.Sym])
                    {
                        F1 = new EAG.Nont;
                        EAG.assign(F1, nont);
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
            if (cast(EAG.Rep) eag.HNont[N].Def)
            {
                F1 = new EAG.Nont;
                F1.Ind = eag.NextHFactor;
                ++eag.NextHFactor;
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
        if (cast(EAG.Opt) eag.HNont[N].Def || cast(EAG.Rep) eag.HNont[N].Def)
        {
            A1 = new EAG.Alt;
            A1.Ind = eag.NextHAlt;
            ++eag.NextHAlt;
            A1.Up = N.to!int;
            A1.Next = null;
            A1.Sub = null;
            A1.Last = null;
            if (auto opt = cast(EAG.Opt) eag.HNont[N].Def)
            {
                A1.Scope = opt.Scope;
                A1.Formal = opt.Formal;
                A1.Pos = opt.EmptyAltPos;
            }
            else if (auto rep = cast(EAG.Rep) eag.HNont[N].Def)
            {
                A1.Scope = rep.Scope;
                A1.Formal = rep.Formal;
                A1.Pos = rep.EmptyAltPos;
            }
            A1.Actual.Params = EAG.empty;
            A1.Actual.Pos = UndefPos;
            A2.Next = A1;
        }
        eag.HNont[N].Def = Def;
    }

    void RestoreNont(size_t N)
    {
        eag.HNont[N].Def = SavedNontDef;
        eag.NextHFactor = SavedNextHFactor;
        eag.NextHAlt = SavedNextHAlt;
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
        int prevOffset;
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
                            error!"variable %s is not defined\n%s"(eag.VarRepr(-Node), eag.ParamBuf[P].Pos);
                            Error = true;
                        }
                        break;
                    default:
                        assert(0);
                    }
                }
                else
                {
                    for (n = 1; n <= eag.MAlt[eag.NodeBuf[Node]].Arity; ++n)
                        Tree(eag.NodeBuf[Node + n]);
                }
            }

            while (eag.ParamBuf[P].Affixform != EAG.nil)
            {
                Def = eag.ParamBuf[P].isDef;
                Tree(eag.ParamBuf[P].Affixform);
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

        A = eag.HNont[N].Def.Sub;
        do
        {
            DefVars[] = false;
            NextEdge = firstEdge;
            NextStack = firstStack;
            TravParams(def, A.Formal.Params, null);
            F = A.Sub;
            Prio = 0;
            Offset = 1;
            prevOffset = 0;
            while (F !is null)
            {
                Factor[F.Ind].Vars = nil;
                Factor[F.Ind].CountAppl = 0;
                Factor[F.Ind].Prio = Prio;
                ++Prio;
                Factor[F.Ind].F = F;
                if (!eag.Pred[(cast(EAG.Nont) F).Sym])
                {
                    FactorOffset[F.Ind] = Offset;
                    prevOffset = Offset;
                    ++Offset;
                }
                else
                {
                    predicatePositionOffset[F.Ind] = prevOffset;
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
        int AltIndex;
        EvalGen.ComputeVarNames(N, No.embed);
        output.write("void P", N, "(TreeType Adr");
        EvalGen.GenFormalParams(N, No.parNeeded);
        output.write(") // ", eag.HNontRepr(N));
        if (eag.HNont[N].anonymous)
            output.write(" in ", eag.NamedHNontRepr(N));
        output.writeln;
        output.writeln("{");
        EvalGen.GenVarDecl(N);
        output.writeln("switch (MOD(Tree[Adr], hyperArityConst))");
        output.writeln("{");
        A = eag.HNont[N].Def.Sub;
        AltIndex = indexOfFirstAlt;
        do
        {
            output.writeln("case ", AltIndex, ":");
            EvalGen.InitScope(A.Scope);
            if (EvalGen.PosNeeded(A.Formal.Params))
                output.writeln("Pos = PosTree[Adr];");
            EvalGen.GenAnalPred(N, A.Formal.Params);
            F = A.Sub;
            while (F !is null)
            {
                if (auto nont = cast(EAG.Nont) F)
                {
                    if (!eag.Pred[nont.Sym])
                    {
                        EvalGen.GenSynPred(N, nont.Actual.Params);
                        output.write("P", nont.Sym, "(Tree[Adr + ", FactorOffset[F.Ind], "]");
                        EvalGen.GenActualParams(nont.Actual.Params, false);
                        output.write("); // ", eag.HNontRepr(nont.Sym));
                        if (eag.HNont[nont.Sym].anonymous)
                            output.write(" in ", eag.NamedHNontRepr(nont.Sym));
                        output.writeln;
                        if (EvalGen.PosNeeded(nont.Actual.Params))
                            output.writeln("Pos = PosTree[Adr + ", FactorOffset[F.Ind], "];");
                        EvalGen.GenAnalPred(N, nont.Actual.Params);
                    }
                    else
                    {
                        EvalGen.GenSynPred(N, nont.Actual.Params);

                        const offset = predicatePositionOffset[F.Ind];

                        if (offset == 0)
                            output.writeln("Pos = PosTree[Adr];");
                        else
                            output.writeln("Pos = PosTree[Tree[Adr + ", offset, "]];");
                        EvalGen.GenPredCall(nont.Sym, nont.Actual.Params);
                        EvalGen.GenAnalPred(N, nont.Actual.Params);
                    }
                }
                F = F.Next;
            }
            EvalGen.GenSynPred(N, A.Formal.Params);
            output.writeln("break;");
            A = A.Next;
            ++AltIndex;
        }
        while (A !is null);
        output.writeln("default:");
        output.writeln("assert(0);");
        output.writeln("}");
        output.writeln("}");
        output.writeln;
    }

    enum fixName = "sweep.fix.d";
    const name = eag.BaseName ~ "Eval";
    const fileName = settings.path(name ~ ".d");

    EvalGen.InitTest;
    Error = Error || !EvalGen.PredsOK();
    if (createMod)
    {
        Fix = Input(fixName, import(fixName));
        output = File(fileName, "w");
        if (!Error)
        {
            EvalGen.InitGen(output, EvalGen.sweepPass, settings);
            InclFix('$');
            output.write(name);
            InclFix('$');
            output.write(HyperArity());
            InclFix('$');
            EvalGen.GenDeclarations(settings);
            EvalGen.GenPredProcs;
            output.writeln;
        }
    }
    Factor = new FactorRecord[eag.NextHFactor + eag.NextHAlt + 1];
    Var = new VarRecord[eag.NextVar + 1];
    Edge = new EdgeRecord[127];
    Stack = new int[eag.NextHFactor + 1];
    DefVars = BitArray();
    DefVars.length = eag.NextVar + 1;
    for (V = EAG.firstVar; V < eag.NextVar; ++V)
        Var[V].Factors = nil;
    foreach (N; GenNonts.bitsSet)
    {
        SaveAndPatchNont(N);
        ComputePermutation(N);
        if (!Error)
        {
            Error = !EvalGen.IsLAG(N);
            if (!Error && createMod)
                GenerateNont(N);
        }
        RestoreNont(N);
    }
    if (createMod)
    {
        if (!Error)
        {
            EmitGen.GenEmitProc(output, settings);
            InclFix('$');
            output.write("P", eag.StartSym);
            InclFix('$');
            EmitGen.GenEmitCall(output, settings);
            InclFix('$');
            EmitGen.GenShowHeap(output);
            InclFix('$');
            output.write(eag.BaseName, "Eval");
            InclFix('$');
            output.close;
        }
        EvalGen.FinitGen;
    }
    EvalGen.FinitTest;
    return fileName;
}

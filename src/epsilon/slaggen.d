module epsilon.slaggen;

import core.time : MonoTime;
import epsilon.eag;
import epsilon.settings;
import io : Input, Position, read;
import log;
import runtime;
import std.algorithm;
import std.bitmanip : BitArray;
import std.stdio : File;
import std.typecons;

public const parsePass = 0;
public const onePass = 1;
public const sweepPass = 2;
public int[] NodeIdent;
public int[] Leaf;
public int[] AffixPlace;
public int[] AffixSpace;

private File output;
private bool SavePos;
private bool UseConst;
private bool UseRefCnt;
private bool TraversePass;
private int[] VarCnt;
private int[] VarAppls;
private bool Testing;
private bool Generating;
private BitArray PreparedHNonts;
private int[] VarDeps;
private int FirstHeap;
private int MaxMAlt;
private long RefConst;
private int[] AffixName;
private BitArray HNontDef;
private int[] HNontVars;
private int[] HNontFVars;
private bool[] RepAppls;
private int[] FormalName;
private int[] VarRefCnt;
private int[] VarDepPos;
private int[] VarName;
private int[] NodeName;
private int IfLevel;
private int[] ActualName;
private BitArray RepVar;
private BitArray EmptySet;

public bool Test()
{
    auto type = Type.slag;

    info!"SLAG testing %s"(eag.BaseName);

    InitTest;
    scope (exit)
        FinitTest;

    foreach (N; eag.Prod.bitsSet)
        if (eag.HNont[N].Id >= 0)
            type = min(type, TestHNont(N, Yes.checkSLAG));

    final switch (type) with (Type)
    {
        case neither:
            info!"%s grammar is no LAG"(eag.BaseName);
            return false;
        case lag:
            info!"%s grammar is no SLAG but LAG"(eag.BaseName);
            return false;
        case slag:
            info!"%s grammar is SLAG"(eag.BaseName);
            return true;
    }
}

public void InitTest() nothrow
{
    if (!Generating && !Testing)
        PrepareInit;
    Testing = true;
}

public void FinitTest() nothrow
{
    if (!Generating)
        PrepareFinit;
    Testing = false;
}

public bool PredsOK()
{
    return eag.Pred.bitsSet
        .map!(N => IsLAG(N))
        .all;
}

public bool IsLAG(size_t N)
{
    return TestHNont(N) != Type.neither;
}

private Type TestHNont(size_t N, Flag!"checkSLAG" checkSLAG = No.checkSLAG)
in (eag.Prod[N])
{
    auto type = Type.slag;

    void CheckDefPos(EAG.ParamRecord param)
    {
        void DefPos(int Node)
        {
            if (Node < 0)
            {
                eag.Var[-Node].Def = true;
            }
            else
            {
                foreach (n; 0 .. eag.MAlt[eag.NodeBuf[Node]].Arity)
                    DefPos(eag.NodeBuf[Node + n + 1]);
            }
        }

        if (param.isDef)
            DefPos(param.Affixform);
    }

    void CheckApplPos(EAG.ParamRecord param)
    {
        void ApplPos(int Node)
        {
            if (Node < 0)
            {
                const V = -Node;

                if (!eag.Var[V].Def)
                {
                    error!"not left-defining\n%s"(eag.Var[V].Pos);
                    type = Type.neither;
                }
            }
            else
            {
                foreach (n; 0 .. eag.MAlt[eag.NodeBuf[Node]].Arity)
                    ApplPos(eag.NodeBuf[Node + n + 1]);
            }
        }

        if (!param.isDef)
            ApplPos(param.Affixform);
    }

    void CheckSLAGCond(EAG.ParamRecord param)
    {
        const Node = param.Affixform;

        if (param.isDef)
        {
            if (Node >= 0)
            {
                error!"cannot analyze bottom up\n%s"(param.Pos);
                type = min(type, Type.lag);
            }
            else if (eag.Var[-Node].Def)
            {
                error!"cannot check for equality bottom up\n%s"(param.Pos);
                type = min(type, Type.lag);
            }
            else if (eag.Var[eag.Var[-Node].Neg].Def)
            {
                error!"cannot check for inequality bottom up\n%s"(param.Pos);
                type = min(type, Type.lag);
            }
            else if (VarAppls[-Node] > 1)
            {
                error!"cannot synthesize %s times bottom up\n%s"(VarAppls[-Node], param.Pos);
                type = min(type, Type.lag);
            }
        }
    }

    Prepare(N);

    EAG.Rule Node = eag.HNont[N].Def;

    if (auto rep = cast(EAG.Rep) Node)
    {
        InitScope(rep.Scope);
        rep.Formal.params(eag).each!(param => CheckDefPos(param));
        rep.Formal.params(eag).each!(param => CheckApplPos(param));
    }
    else if (auto opt = cast(EAG.Opt) Node)
    {
        InitScope(opt.Scope);
        opt.Formal.params(eag).each!(param => CheckDefPos(param));
        opt.Formal.params(eag).each!(param => CheckApplPos(param));
    }

    EAG.Alt A = Node.Sub;

    do
    {
        InitScope(A.Scope);
        A.Formal.params(eag).each!(param => CheckDefPos(param));

        EAG.Factor F = A.Sub;

        while (F !is null)
        {
            if (auto nont = cast(EAG.Nont) F)
            {
                nont.Actual.params(eag).each!(param => CheckApplPos(param));
                if (checkSLAG && eag.HNont[nont.Sym].anonymous && eag.Prod[nont.Sym])
                    type = min(type, TestHNont(nont.Sym, checkSLAG));
                nont.Actual.params(eag).each!(param => CheckDefPos(param));
            }
            F = F.Next;
        }
        if (cast(EAG.Rep) Node !is null)
        {
            A.Actual.params(eag).each!(param => CheckApplPos(param));
            foreach (param; A.Actual.params(eag))
            {
                if (checkSLAG)
                    CheckSLAGCond(param);
                CheckDefPos(param);
            }
        }
        A.Formal.params(eag).each!(param => CheckApplPos(param));
        A = A.Next;
    }
    while (A !is null);
    return type;
}

private enum Type
{
    neither,
    lag,
    slag,
}

private void Prepare(size_t N) nothrow
{
    void Traverse(EAG.ParamRecord[] params)
    {
        void DefPos(int Node)
        {
            if (Node < 0)
            {
                ++VarCnt[-Node];
            }
            else
            {
                foreach (n; 0 .. eag.MAlt[eag.NodeBuf[Node]].Arity)
                    DefPos(eag.NodeBuf[Node + n + 1]);
            }
        }

        void ApplPos(int Node)
        {
            if (Node < 0)
            {
                ++VarCnt[-Node];
                ++VarAppls[-Node];
            }
            else
            {
                foreach (n; 0 .. eag.MAlt[eag.NodeBuf[Node]].Arity)
                    ApplPos(eag.NodeBuf[Node + n + 1]);
            }
        }

        foreach (param; params)
            if (param.isDef)
                DefPos(param.Affixform);
            else
                ApplPos(param.Affixform);
    }

    void InitArray(EAG.ScopeDesc Scope)
    {
        foreach (i; Scope.Beg .. Scope.End)
        {
            VarCnt[i] = 0;
            VarAppls[i] = 0;
        }
    }

    if (!PreparedHNonts[N])
    {
        EAG.Rule Node = eag.HNont[N].Def;

        if (auto rep = cast(EAG.Rep) Node)
        {
            InitArray(rep.Scope);
            Traverse(rep.Formal.params(eag));
        }
        else if (auto opt = cast(EAG.Opt) Node)
        {
            InitArray(opt.Scope);
            Traverse(opt.Formal.params(eag));
        }

        EAG.Alt A = Node.Sub;

        do
        {
            InitArray(A.Scope);
            Traverse(A.Formal.params(eag));

            EAG.Factor F = A.Sub;

            while (F !is null)
            {
                if (auto nont = cast(EAG.Nont) F)
                    Traverse(nont.Actual.params(eag));
                F = F.Next;
            }
            if (cast(EAG.Rep) Node !is null)
            {
                Traverse(A.Actual.params(eag));
                foreach (param; A.Actual.params(eag))
                    if (param.isDef && param.Affixform < 0)
                        RepVar[-param.Affixform] = true;
            }
            A = A.Next;
        }
        while (A !is null);
        PreparedHNonts[N] = true;
    }
}

public void InitGen(File MOut, int Treatment, Settings settings)
{
    void SetFlags(int Treatment)
    {
        switch (Treatment)
        {
        case parsePass:
            SavePos = true;
            UseConst = false;
            UseRefCnt = false;
            break;
        case onePass:
            break;
        case sweepPass:
            TraversePass = true;
            break;
        default:
            assert(0);
        }
    }

    if (Generating)
        trace!"resetting SLAG";
    output = MOut;
    SavePos = false;
    TraversePass = false;
    UseConst = !settings.c;
    UseRefCnt = !settings.r;
    SetFlags(Treatment);
    info!"%s %s"(UseRefCnt ? "+rc" : "-rc", UseConst ? "+ct" : "-ct");
    if (!Testing)
        PrepareInit;
    ComputeNodeIdent;
    ComputeConstDat;
    AffixName = new int[eag.NextParam];
    foreach (i; EAG.firstParam .. eag.NextParam)
        AffixName[i] = -1;
    NodeName = new int[eag.NextNode];
    VarName = new int[eag.NextVar];
    VarDeps = new int[eag.NextVar];
    VarRefCnt = new int[eag.NextVar];
    VarDepPos = new int[eag.NextVar];
    foreach (i; EAG.firstVar .. eag.NextVar)
    {
        VarRefCnt[i] = 0;
        VarDepPos[i] = -1;
        VarName[i] = -1;
    }
    ActualName = new int[eag.NextDom];
    FormalName = new int[eag.NextDom];
    foreach (i; EAG.firstDom .. eag.NextDom)
    {
        ActualName[i] = -1;
        FormalName[i] = -1;
    }
    HNontVars = new int[eag.NextHNont];
    HNontFVars = new int[eag.NextHNont];
    HNontDef = BitArray();
    HNontDef.length = eag.NextHNont + 1;
    RepAppls = new bool[eag.NextHNont];
    foreach (i; EAG.firstHNont .. eag.NextHNont)
        RepAppls[i] = true;
    EmptySet = BitArray();
    EmptySet.length = eag.NextVar + 1;
    Generating = true;
}

private void PrepareInit() nothrow
{
    VarCnt = new int[eag.NextVar];
    VarAppls = new int[eag.NextVar];
    RepVar = BitArray();
    RepVar.length = eag.NextVar + 1;
    PreparedHNonts = BitArray();
    PreparedHNonts.length = eag.NextHNont + 1;
}

private void ComputeNodeIdent() nothrow @safe
{
    int i;

    NodeIdent = new int[eag.NextMAlt];
    foreach (A; EAG.firstMAlt .. eag.NextMAlt)
        NodeIdent[A] = -1;
    MaxMAlt = 0;
    foreach (N; EAG.firstMNont .. eag.NextMNont)
    {
        int A = eag.MNont[N].MRule;

        i = 0;
        while (A != EAG.nil)
        {
            ++i;
            NodeIdent[A] = i;
            A = eag.MAlt[A].Next;
        }
        if (i > MaxMAlt)
            MaxMAlt = i;
    }
    i = 1;
    while (i <= MaxMAlt)
        i = i * 2;
    MaxMAlt = i;
    RefConst = 0;
    foreach (A; EAG.firstMAlt .. eag.NextMAlt)
    {
        assert(NodeIdent[A] >= 0);

        NodeIdent[A] = NodeIdent[A] + eag.MAlt[A].Arity * MaxMAlt;
        if (RefConst < NodeIdent[A])
            RefConst = NodeIdent[A];
    }
    i = 1;
    while (i <= RefConst)
        i = i * 2;
    RefConst = i;
}

private void ComputeConstDat() nothrow
{
    void Traverse(size_t N, ref int ConstPtr)
    {
        void CheckParams(int P, ref int ConstPtr)
        {
            bool isConst;

            void TraverseTree(int Node, ref int Next)
            {
                if (Node < 0)
                {
                    isConst = false;
                }
                else
                {
                    const Arity = eag.MAlt[eag.NodeBuf[Node]].Arity;

                    if (!UseConst || Arity != 0)
                        Next += 1 + Arity;
                    foreach (n; 0 .. Arity)
                        TraverseTree(eag.NodeBuf[Node + n + 1], Next);
                }
            }

            while (eag.ParamBuf[P].Affixform != EAG.nil)
            {
                const Tree = eag.ParamBuf[P].Affixform;

                isConst = true;
                TraverseTree(Tree, AffixSpace[P]);
                if (Tree > 0 && eag.MAlt[eag.NodeBuf[Tree]].Arity == 0)
                {
                    if (isConst)
                        AffixPlace[P] = Leaf[eag.NodeBuf[Tree]];
                }
                else
                {
                    if (isConst)
                    {
                        AffixPlace[P] = ConstPtr;
                        ConstPtr += AffixSpace[P];
                    }
                }
                ++P;
            }
        }

        EAG.Rule Node = eag.HNont[N].Def;

        if (auto rep = cast(EAG.Rep) Node)
            CheckParams(rep.Formal.Params, ConstPtr);
        else if (auto opt = cast(EAG.Opt) Node)
            CheckParams(opt.Formal.Params, ConstPtr);

        EAG.Alt A = Node.Sub;

        do
        {
            CheckParams(A.Formal.Params, ConstPtr);

            EAG.Factor F = A.Sub;

            while (F !is null)
            {
                if (auto nont = cast(EAG.Nont) F)
                    CheckParams(nont.Actual.Params, ConstPtr);
                F = F.Next;
            }
            if (cast(EAG.Rep) Node)
                CheckParams(A.Actual.Params, ConstPtr);
            A = A.Next;
        }
        while (A !is null);
    }

    AffixSpace = new int[eag.NextParam];
    AffixPlace = new int[eag.NextParam];
    foreach (i; EAG.firstParam .. eag.NextParam)
    {
        AffixSpace[i] = 0;
        AffixPlace[i] = -1;
    }
    Leaf = new int[eag.NextMAlt];

    int ConstPtr = eag.MaxMArity + 1;

    FirstHeap = ConstPtr;
    foreach (A; EAG.firstMAlt .. eag.NextMAlt)
    {
        if (eag.MAlt[A].Arity == 0)
        {
            Leaf[A] = ConstPtr;
            ++ConstPtr;
        }
        else
        {
            Leaf[A] = -1;
        }
    }
    foreach (i; eag.Prod.bitsSet)
        Traverse(i, ConstPtr);
    if (UseConst)
        FirstHeap = ConstPtr;
}

public void FinitGen()
{
    if (!Testing)
        PrepareFinit;
    EmptySet.length = 0;
    NodeIdent = null;
    AffixSpace = null;
    AffixPlace = null;
    Leaf = null;
    AffixName = null;
    NodeName = null;
    VarName = null;
    VarDeps = null;
    VarRefCnt = null;
    VarDepPos = null;
    ActualName = null;
    FormalName = null;
    HNontVars = null;
    HNontFVars = null;
    RepAppls = null;
    Generating = false;
}

private void PrepareFinit() nothrow
{
    VarCnt = null;
    VarAppls = null;
    RepVar.length = 0;
    PreparedHNonts.length = 0;
}

public void GenRepStart(int Sym) @safe
{
    if (!UseRefCnt)
    {
        import std.conv : to;

        const Next = (cast(EAG.Rep) eag.HNont[Sym].Def).Sub.Formal.params(eag)
            .count!(param => !param.isDef)
            .to!int;

        GenOverflowGuard(Next);
    }

    int Dom = eag.HNont[Sym].Sig;
    int P = (cast(EAG.Rep) eag.HNont[Sym].Def).Sub.Formal.Params;

    while (eag.DomBuf[Dom] != EAG.nil)
    {
        if (!eag.ParamBuf[P].isDef)
        {
            if (UseRefCnt)
            {
                output.write("GetHeap(0, ");
                GenVar(FormalName[Dom]);
                output.write("); ");
            }
            else
            {
                GenVar(FormalName[Dom]);
                output.write(" = NextHeap; ++NextHeap; ");
            }
            GenVar(AffixName[P]);
            output.write(" = ");
            GenVar(FormalName[Dom]);
            output.writeln(";");
        }
        ++P;
        ++Dom;
    }
}

public void GenDeclarations(Settings settings)
{
    Input Fix;

    void InclFix(char Term)
    {
        import std.conv : to;
        import std.exception : enforce;

        char c = Fix.front.to!char;

        while (c != Term)
        {
            enforce(c != 0,
                    "error: unexpected end of eSLAGGen.fix.d");

            output.write(c);
            Fix.popFront;
            c = Fix.front.to!char;
        }
        Fix.popFront;
    }

    void SkipFix(char Term)
    {
        import std.conv : to;
        import std.exception : enforce;

        char c = Fix.front.to!char;

        while (c != Term)
        {
            enforce(c != 0,
                    "error: unexpected end of eSLAGGen.fix.d");

            Fix.popFront;
            c = Fix.front.to!char;
        }
        Fix.popFront;
    }

    void GenTabFile(string name, long TabTimeStamp)
    {
        const errVal = 0;
        const magic = 1_818_326_597;
        int[] Heap;

        void SynTree(int Node, ref int Next)
        {
            const Next1 = Next;

            Heap[Next] = NodeIdent[eag.NodeBuf[Node]];
            Next += 1 + eag.MAlt[eag.NodeBuf[Node]].Arity;
            foreach (n; 0 .. eag.MAlt[eag.NodeBuf[Node]].Arity)
            {
                const Node1 = eag.NodeBuf[Node + n + 1];

                if (eag.MAlt[eag.NodeBuf[Node1]].Arity == 0)
                {
                    Heap[Next1 + n + 1] = Leaf[eag.NodeBuf[Node1]];
                }
                else
                {
                    Heap[Next1 + n + 1] = Next;
                    SynTree(Node1, Next);
                }
            }
        }

        File Tab = File(settings.path(name), "w");

        Tab.writefln!"long %s"(magic);
        Tab.writefln!"long %s"(TabTimeStamp);
        Tab.writefln!"long %s"(FirstHeap - 1);
        Heap = new int[FirstHeap];
        Heap[errVal] = 0;
        foreach (i; 0 .. eag.MaxMArity)
            Heap[i + 1] = errVal;
        if (UseConst)
        {
            foreach (i; EAG.firstMAlt .. eag.NextMAlt)
            {
                if (Leaf[i] >= errVal)
                    Heap[Leaf[i]] = NodeIdent[i];
            }
            foreach (P; EAG.firstParam .. eag.NextParam)
            {
                if (eag.ParamBuf[P].Affixform != EAG.nil && AffixPlace[P] >= 0)
                {
                    int Next = AffixPlace[P];

                    SynTree(eag.ParamBuf[P].Affixform, Next);
                }
            }
        }
        foreach (i; 0 .. FirstHeap)
            Tab.writefln!"long %s"(Heap[i]);
        Tab.writefln!"long %s"(TabTimeStamp);
    }

    enum fixName = "slaggen.fix.d";
    const name = eag.BaseName ~ (TraversePass ? "Eval.EvalTab" : ".EvalTab");
    const TabTimeStamp = MonoTime.currTime.ticks;

    Fix = Input(fixName, import(fixName));
    InclFix('$');
    output.write(FirstHeap - 1);
    InclFix('$');
    output.write(MaxMAlt);
    InclFix('$');
    if (SavePos)
        output.write("Eval.TreeType");
    else
        output.write("long");
    InclFix('$');
    if (SavePos)
        output.write("Eval.TreeType[]");
    else
        output.write("HeapType[]");
    InclFix('$');
    if (SavePos)
        InclFix('$');
    else
        SkipFix('$');
    InclFix('$');
    output.write(eag.MaxMArity + 1);
    InclFix('$');
    output.write(RefConst);
    InclFix('$');
    if (SavePos)
    {
        SkipFix('$');
        InclFix('$');
    }
    else
    {
        InclFix('$');
        SkipFix('$');
    }
    if (UseRefCnt)
    {
        InclFix('$');
        SkipFix('$');
    }
    else
    {
        SkipFix('$');
        InclFix('$');
    }
    InclFix('$');
    if (!TraversePass)
        output.write("S.");
    InclFix('$');
    if (!TraversePass)
        output.write("Pred");
    InclFix('$');
    if (UseRefCnt)
        InclFix('$');
    else
        SkipFix('$');
    InclFix('$');
    output.write(name);
    InclFix('$');
    output.write(TabTimeStamp);
    InclFix('$');
    if (SavePos)
        InclFix('$');
    else
        SkipFix('$');
    InclFix('$');
    GenTabFile(name, TabTimeStamp);
}

public bool PosNeeded(int P) @nogc nothrow @safe
{
    while (eag.ParamBuf[P].Affixform != EAG.nil)
    {
        if (eag.ParamBuf[P].isDef)
        {
            const V = -eag.ParamBuf[P].Affixform;

            if (V < 0)
                return true;
            else if (eag.Var[V].Def)
                return true;
            else if (eag.Var[eag.Var[V].Neg].Def)
                return true;
        }
        ++P;
    }
    return false;
}

public void GenRepAlt(int Sym, EAG.Alt A)
{
    int P;
    int P1;
    int Dom;
    const Guard = !RepAppls[Sym];

    GenSynPred(Sym, A.Actual.Params);
    if (SavePos)
        output.writeln("PushPos;");
    P = A.Actual.Params;
    Dom = eag.HNont[Sym].Sig;
    while (eag.ParamBuf[P].Affixform != EAG.nil)
    {
        if (!eag.ParamBuf[P].isDef && AffixName[P] != FormalName[Dom])
        {
            GenVar(FormalName[Dom]);
            output.write(" = ");
            GenVar(AffixName[P]);
            output.writeln(";");
        }
        ++P;
        ++Dom;
    }
    P1 = A.Actual.Params;
    Dom = eag.HNont[Sym].Sig;
    P = A.Formal.Params;
    if (!UseRefCnt)
        GetAffixSpace(P);
    GenHangIn(P, Guard);

    int Next = 0;

    while (eag.ParamBuf[P].Affixform != EAG.nil)
    {
        if (!eag.ParamBuf[P].isDef)
        {
            const Tree = eag.ParamBuf[P].Affixform;

            if (SavePos)
                output.writeln("PopPos(", eag.MAlt[eag.NodeBuf[Tree]].Arity, ");");
            if (Tree > 0 && !(UseConst && AffixPlace[P] >= 0))
            {
                if (Guard)
                {
                    output.write("if (");
                    GenVar(NodeName[Tree]);
                    output.writeln(" != undef)");
                    output.writeln("{");
                }
                if (UseRefCnt)
                    Gen1SynTree(Tree, RepVar, eag.Pred[Sym]);
                else
                    GenSynTree(Tree, RepVar, Next);
                output.writeln;
                if (Guard)
                    output.writeln("}");
            }
            if (Guard && VarAppls[-eag.ParamBuf[P1].Affixform] == 0)
            {
                GenVar(AffixName[P1]);
                output.writeln(" = undef;");
            }
        }
        ++P;
        ++P1;
        ++Dom;
    }
    if (!UseRefCnt)
        GenHeapInc(Next);
}

public void GenRepEnd(int Sym)
{
    const Guard = false; // TODO: eliminate dead code?

    InitScope((cast(EAG.Rep) eag.HNont[Sym].Def).Scope);

    int P = (cast(EAG.Rep) eag.HNont[Sym].Def).Formal.Params;
    int P1 = eag.HNont[Sym].Def.Sub.Actual.Params;
    int Dom = eag.HNont[Sym].Sig;
    int Next = 0;

    GenAnalPred(Sym, P);
    if (!UseRefCnt)
        GetAffixSpace(P);
    GenHangIn(P, Guard);
    while (eag.ParamBuf[P].Affixform != EAG.nil)
    {
        if (!eag.ParamBuf[P].isDef)
        {
            const Tree = eag.ParamBuf[P].Affixform;

            if (SavePos)
                output.writeln("PopPos(", eag.MAlt[eag.NodeBuf[Tree]].Arity, ");");
            if (Tree > 0 && !(UseConst && AffixPlace[P] >= 0))
            {
                if (Guard)
                {
                    output.write("if (");
                    GenVar(NodeName[Tree]);
                    output.writeln(" != undef)");
                    output.writeln("{");
                }
                if (UseRefCnt)
                    Gen1SynTree(Tree, EmptySet, eag.Pred[Sym]);
                else
                    GenSynTree(Tree, EmptySet, Next);
                output.writeln("");
                if (Guard)
                    output.writeln("}");
            }
            if (UseRefCnt)
            {
                GenVar(AffixName[P]);
                output.write(" = ");
                GenVar(FormalName[Dom]);
                output.write("; ");
            }
            GenVar(FormalName[Dom]);
            output.write(" = ");
            GenHeap(FormalName[Dom], 0);
            output.writeln(";");
            if (UseRefCnt)
            {
                GenHeap(AffixName[P], 0);
                output.writeln(" = 0;");
                output.write("FreeHeap(");
                GenVar(AffixName[P]);
                output.writeln(");");
            }
        }
        ++P;
        ++P1;
        ++Dom;
    }
    if (!UseRefCnt)
        GenHeapInc(Next);
}

private void GenHangIn(int P, bool Guard)
{
    void FreeVariables(int Node)
    {
        if (Node < 0)
        {
            if (!RepVar[-Node])
            {
                output.write("FreeHeap(");
                GenVar(VarName[-Node]);
                output.write("); ");
            }
        }
        else
        {
            foreach (n; 0 .. eag.MAlt[eag.NodeBuf[Node]].Arity)
                FreeVariables(eag.NodeBuf[Node + n + 1]);
        }
    }

    int Next = 0;

    while (eag.ParamBuf[P].Affixform != EAG.nil)
    {
        if (!eag.ParamBuf[P].isDef)
        {
            const Tree = eag.ParamBuf[P].Affixform;
            if (Guard)
            {
                output.write("if (");
                GenVar(AffixName[P]);
                output.writeln(" != undef)");
                output.writeln("{");
            }
            if (UseConst && AffixPlace[P] >= 0)
            {
                GenHeap(AffixName[P], 0);
                output.writeln(" = ", AffixPlace[P], ";");
                if (UseRefCnt)
                    GenIncRefCnt(-AffixPlace[P], 1);
            }
            else if (Tree < 0)
            {
                if (AffixName[P] != VarName[-Tree])
                {
                    GenHeap(AffixName[P], 0);
                    output.write(" = ");
                    GenVar(VarName[-Tree]);
                    output.writeln(";");
                    if (Guard)
                    {
                        output.writeln("}");
                        output.writeln("else");
                        output.writeln("{");
                        output.write("FreeHeap(");
                        GenVar(VarName[-Tree]);
                        output.writeln(");");
                    }
                }
            }
            else
            {
                if (UseRefCnt)
                {
                    output.write("GetHeap(", eag.MAlt[eag.NodeBuf[Tree]].Arity, ", ");
                    GenVar(NodeName[Tree]);
                    output.write("); ");
                    GenHeap(AffixName[P], 0);
                    output.write(" = ");
                    GenVar(NodeName[Tree]);
                    output.writeln(";");
                    if (Guard)
                    {
                        output.writeln("}");
                        output.writeln("else");
                        output.writeln("{");
                        FreeVariables(Tree);
                    }
                }
                else
                {
                    GenHeap(AffixName[P], 0);
                    output.write(" = NextHeap");
                    if (Next != 0)
                        output.write(" + ", Next);
                    output.writeln(";");
                    Next += AffixSpace[P];
                    if (Guard)
                    {
                        output.writeln("}");
                        output.writeln("else");
                        output.writeln("{");
                    }
                }
                if (Guard)
                {
                    GenVar(NodeName[Tree]);
                    output.writeln(" = undef;");
                }
            }
            if (Guard)
                output.writeln("}");
        }
        ++P;
    }
}

public void GenPredProcs()
{
    void GenPredCover(size_t N)
    in (eag.Pred[N])
    {
        output.write("void Check", N, "(string ErrMsg");
        GenFormalParams(N, No.parNeeded);
        output.writeln(")");
        output.writeln("{");
        output.write("if (!Pred", N, "(");

        int Dom = eag.HNont[N].Sig;
        int i = 1;

        if (eag.DomBuf[Dom] != EAG.nil)
        {
            for (;;)
            {
                GenVar(i);
                ++Dom;
                ++i;
                if (eag.DomBuf[Dom] == EAG.nil)
                    break;
                output.write(", ");
            }
        }
        output.writeln("))");
        output.writeln("{");
        Dom = eag.HNont[N].Sig;
        i = 1;
        while (eag.DomBuf[Dom] > 0)
            ++Dom;
        if (eag.DomBuf[Dom] != EAG.nil)
        {
            output.write("if (");
            for (;;)
            {
                GenVar(i);
                output.write(" != errVal");
                do
                {
                    ++Dom;
                    ++i;
                }
                while (!(eag.DomBuf[Dom] <= 0));
                if (eag.DomBuf[Dom] == EAG.nil)
                    break;
                output.write(" && ");
            }
            output.writeln(")");
            output.writeln("PredError(ErrMsg);");
        }
        else
        {
            output.write("Error(ErrMsg);");
        }
        output.writeln("}");
        output.writeln("}");
        output.writeln;
    }

    void GenPredicateCode(size_t N)
    {
        EAG.Rule Node = eag.HNont[N].Def;
        EAG.Alt A;

        void CleanLevel(int Level)
        {
            if (Level >= 1)
            {
                foreach (i; 0 .. Level)
                    output.write("} ");
                output.writeln;
            }
        }

        void FreeParamTrees(int P)
        {
            while (eag.ParamBuf[P].Affixform != EAG.nil)
            {
                if (eag.ParamBuf[P].isDef)
                    GenFreeHeap(AffixName[P]);
                ++P;
            }
        }

        void TraverseFactor(EAG.Factor F, int FormalParams)
        {
            if (F !is null)
            {
                auto nont = cast(EAG.Nont) F;

                assert(nont !is null);
                assert(eag.Pred[nont.Sym]);

                GenSynPred(N, nont.Actual.Params);
                output.write("if (Pred", nont.Sym);
                GenActualParams(nont.Actual.Params, true);
                output.writeln(") // ", eag.HNontRepr(nont.Sym));
                output.writeln("{");
                GenAnalPred(N, nont.Actual.Params);

                const Level = IfLevel;

                TraverseFactor(F.Next, FormalParams);
                CleanLevel(Level);
                output.writeln("}");
                if (UseRefCnt)
                    FreeParamTrees(nont.Actual.Params);
            }
            else
            {
                if (cast(EAG.Rep) Node)
                {
                    GenSynPred(N, A.Actual.Params);
                    output.write("if (Pred", N);
                    GenActualParams(A.Actual.Params, true);
                    output.writeln(") // ", eag.HNontRepr(N));
                    output.writeln("{");
                    GenAnalPred(N, A.Actual.Params);

                    const Level = IfLevel;

                    GenSynPred(N, FormalParams);
                    output.writeln("Failed = false;");
                    CleanLevel(Level);
                    output.writeln("}");
                    if (UseRefCnt)
                        FreeParamTrees(A.Actual.Params);
                }
                else
                {
                    GenSynPred(N, FormalParams);
                    output.writeln("Failed = false;");
                }
            }
        }

        int AltLevel = 0;
        int P;

        output.writeln("Failed = true;");
        if (cast(EAG.Rep) Node || cast(EAG.Opt) Node)
        {
            EAG.ScopeDesc Scope;

            if (auto opt = cast(EAG.Opt) Node)
            {
                P = opt.Formal.Params;
                Scope = opt.Scope;
            }
            else if (auto rep = cast(EAG.Rep) Node)
            {
                P = rep.Formal.Params;
                Scope = rep.Scope;
            }
            InitScope(Scope);
            GenAnalPred(N, P);

            const Level = IfLevel;

            GenSynPred(N, P);
            output.writeln("Failed = false;");
            CleanLevel(Level);
            ++AltLevel;
        }
        A = Node.Sub;
        for (;;)
        {
            if (AltLevel > 0)
            {
                output.writeln("if (Failed) // alternative #", AltLevel + 1);
                output.writeln("{");
            }
            InitScope(A.Scope);
            GenAnalPred(N, A.Formal.Params);

            const Level = IfLevel;

            TraverseFactor(A.Sub, A.Formal.Params);
            CleanLevel(Level);
            ++AltLevel;
            A = A.Next;
            if (A is null)
            {
                break;
            }
        }
        foreach (i; 1 .. AltLevel)
            output.write("} ");
        output.writeln;
        P = Node.Sub.Formal.Params;
        if (UseRefCnt)
            FreeParamTrees(P);
        output.writeln("if (Failed)");
        output.writeln("{");
        while (eag.ParamBuf[P].Affixform != EAG.nil)
        {
            if (!eag.ParamBuf[P].isDef)
            {
                GenVar(AffixName[P]);
                output.writeln(" = errVal;");
                if (UseRefCnt)
                    output.writeln("Heap[errVal] += refConst;");
            }
            ++P;
        }
        output.writeln("}");
    }

    foreach (N; eag.Pred.bitsSet)
        GenPredCover(N);
    foreach (N; eag.Pred.bitsSet)
    {
        ComputeVarNames(N, No.embed);
        output.write("bool Pred", N);
        GenFormalParams(N, Yes.parNeeded);
        output.writeln(" // ", eag.HNontRepr(N));
        output.writeln("{");
        GenVarDecl(N);
        GenPredicateCode(N);
        output.writeln("return !Failed;");
        output.writeln("}");
        output.writeln;
    }
}

public void ComputeVarNames(size_t N, Flag!"embed" embed)
in (eag.Prod[N])
in (!HNontDef[N])
{
    int[] FreeVar;
    int[] RefCnt;
    int Top;
    int NextFreeVar;

    void VarExpand()
    {
        if (NextFreeVar >= RefCnt.length)
        {
            auto Int = new int[2 * RefCnt.length];

            foreach (i; 0 .. NextFreeVar)
                Int[i] = RefCnt[i];
            foreach (i; NextFreeVar .. Int.length)
                Int[i] = 0;
            RefCnt = Int;
        }
        if (Top >= FreeVar.length)
        {
            auto Int = new int[2 * FreeVar.length];

            foreach (i; 0 .. Top)
                Int[i] = FreeVar[i];
            FreeVar = Int;
        }
    }

    int GetFreeVar()
    {
        int Var;

        if (Top > 0)
        {
            --Top;
            Var = FreeVar[Top];
        }
        else
        {
            ++NextFreeVar;
            if (NextFreeVar >= RefCnt.length)
                VarExpand;
            RefCnt[NextFreeVar] = 0;
            Var = NextFreeVar;
        }
        trace!"RC: -%s"(Var);
        return Var;
    }

    void Dispose(int Var)
    {
        --RefCnt[Var];
        if (RefCnt[Var] == 0)
        {
            trace!"RC: +%s"(Var);
            FreeVar[Top] = Var;
            ++Top;
            if (Top >= FreeVar.length)
                VarExpand;
        }
    }

    void Traverse(size_t N)
    {
        EAG.Rule Node;
        EAG.Alt A;
        EAG.Factor F;
        int P;
        int Tree;
        bool isPred;

        void CheckDefPos(int P)
        {
            void DefPos(int Node, int Var)
            {
                if (Node < 0)
                {
                    const V = -Node;

                    if (!eag.Var[V].Def)
                    {
                        eag.Var[V].Def = true;
                        if (VarName[V] < 0)
                        {
                            VarName[V] = GetFreeVar;
                            ++RefCnt[VarName[V]];
                        }
                        if (eag.Var[eag.Var[V].Neg].Def)
                        {
                            const Vn = eag.Var[V].Neg;

                            --VarDeps[V];
                            --VarDeps[Vn];
                            if (VarDeps[Vn] == 0)
                            {
                                VarDepPos[Vn] = P;
                                Dispose(VarName[Vn]);
                            }
                        }
                    }
                    else
                    {
                        if (VarDeps[V] == 1)
                            VarDepPos[V] = P;
                    }
                    --VarDeps[V];
                    if (VarDeps[V] == 0)
                        Dispose(VarName[V]);
                }
                else
                {
                    const Arity = eag.MAlt[eag.NodeBuf[Node]].Arity;

                    if (Arity != 0)
                        NodeName[Node] = Var;
                    foreach (n; 0 .. Arity)
                    {
                        const Node1 = eag.NodeBuf[Node + n + 1];
                        const NeedVar = ((isPred || UseRefCnt) && Var == AffixName[P] || n + 1 != Arity)
                            && Node1 >= 0
                            && eag.MAlt[eag.NodeBuf[Node1]].Arity > 0;
                        int Var1;

                        if (NeedVar)
                        {
                            Var1 = GetFreeVar;
                            ++RefCnt[Var1];
                        }
                        else
                        {
                            Var1 = Var;
                        }
                        DefPos(Node1, Var1);
                        if (NeedVar)
                            Dispose(Var1);
                    }
                }
            }

            while (eag.ParamBuf[P].Affixform != EAG.nil)
            {
                const Tree = eag.ParamBuf[P].Affixform;

                if (eag.ParamBuf[P].isDef)
                {
                    if (Tree < 0 && VarName[-Tree] < 0)
                    {
                        const V = -Tree;

                        VarName[V] = AffixName[P];
                        ++RefCnt[VarName[V]];
                    }
                    DefPos(Tree, AffixName[P]);
                }
                ++P;
            }
        }

        void CheckApplPos(int P, bool Repetition)
        {
            int Tree;
            int V;
            int P1;

            void ApplPos(int Node, int Var)
            {
                if (Node < 0)
                {
                    const V = -Node;

                    --VarDeps[V];
                    if (VarDeps[V] == 0)
                        Dispose(VarName[V]);
                    if (VarDepPos[V] >= 0)
                        VarDepPos[V] = -1;
                }
                else
                {
                    const Arity = eag.MAlt[eag.NodeBuf[Node]].Arity;

                    NodeName[Node] = Var;
                    foreach (n; 0 .. Arity)
                    {
                        const Node1 = eag.NodeBuf[Node + n + 1];
                        const NeedVar = !(UseConst && AffixPlace[P] > 0)
                            && UseRefCnt
                            && (Var == AffixName[P] || n + 1 != Arity)
                            && Node1 >= 0
                            && eag.MAlt[eag.NodeBuf[Node1]].Arity > 0;
                        int Var1;

                        if (NeedVar)
                        {
                            Var1 = GetFreeVar;
                            ++RefCnt[Var1];
                        }
                        else
                        {
                            Var1 = Var;
                        }
                        ApplPos(Node1, Var1);
                        if (NeedVar)
                            Dispose(Var1);
                    }
                }
            }

            P1 = P;
            while (eag.ParamBuf[P].Affixform != EAG.nil)
            {
                if (!eag.ParamBuf[P].isDef)
                {
                    Tree = eag.ParamBuf[P].Affixform;
                    if (Tree < 0 && VarName[-Tree] < 0)
                    {
                        V = -Tree;
                        VarName[V] = AffixName[P];
                        ++RefCnt[VarName[V]];
                    }
                    if (!(UseConst && AffixPlace[P] > 0) && Repetition && Tree >= 0)
                    {
                        NodeName[Tree] = GetFreeVar;
                        ++RefCnt[NodeName[Tree]];
                        ApplPos(Tree, NodeName[Tree]);
                    }
                    else
                    {
                        ApplPos(Tree, AffixName[P]);
                    }
                }
                ++P;
            }
            if (Repetition)
            {
                while (eag.ParamBuf[P1].Affixform != EAG.nil)
                {
                    if (!eag.ParamBuf[P1].isDef && !(UseConst && AffixPlace[P1] > 0))
                    {
                        Tree = eag.ParamBuf[P1].Affixform;
                        if (Tree >= 0)
                            Dispose(NodeName[Tree]);
                    }
                    ++P1;
                }
            }
        }

        void GetFormalParamNames(size_t N, int P)
        {
            const Repetition = !eag.Pred[N] && cast(EAG.Rep) eag.HNont[N].Def;
            int Dom = eag.HNont[N].Sig;
            int Tree;
            int V;

            while (eag.ParamBuf[P].Affixform != EAG.nil)
            {
                if (Repetition)
                {
                    AffixName[P] = ActualName[Dom];
                }
                else
                {
                    AffixName[P] = FormalName[Dom];
                    Tree = eag.ParamBuf[P].Affixform;
                    if (!eag.ParamBuf[P].isDef && Tree < 0)
                    {
                        V = -Tree;
                        VarName[V] = AffixName[P];
                        ++RefCnt[VarName[V]];
                    }
                }
                ++P;
                ++Dom;
            }
        }

        void GetActualParamNames(size_t N, int P)
        {
            int FindVarName(int P, int VarName)
            {
                while (AffixName[P] != VarName)
                    ++P;
                return P;
            }

            const Repetition = !eag.Pred[N] && cast(EAG.Rep) eag.HNont[N].Def;
            int P1 = P;
            int Tree;
            int V;

            while (eag.ParamBuf[P].Affixform != EAG.nil)
            {
                Tree = eag.ParamBuf[P].Affixform;
                if (AffixName[P] < 0)
                {
                    if (Tree < 0 && VarName[-Tree] >= 0)
                    {
                        V = -Tree;
                        if (!eag.ParamBuf[P].isDef)
                        {
                            if (Repetition && VarDeps[V] > 1)
                            {
                                AffixName[P] = GetFreeVar;
                            }
                            else if (!eag.Pred[N] && eag.HNont[N].anonymous)
                            {
                                AffixName[P] = VarName[V];
                                if (FindVarName(P1, VarName[V]) != P)
                                    AffixName[P] = GetFreeVar;
                            }
                            else
                            {
                                AffixName[P] = VarName[V];
                            }
                        }
                        else
                        {
                            AffixName[P] = VarName[V];
                            if (eag.Var[V].Def || FindVarName(P1, VarName[V]) != P)
                                AffixName[P] = GetFreeVar;
                        }
                    }
                    else
                    {
                        AffixName[P] = GetFreeVar;
                    }
                }
                ++RefCnt[AffixName[P]];
                if (isPred && eag.ParamBuf[P].isDef)
                    ++RefCnt[AffixName[P]];
                ++P;
            }
        }

        void FreeActualParamNames(int P)
        {
            while (eag.ParamBuf[P].Affixform != EAG.nil)
            {
                Dispose(AffixName[P]);
                ++P;
            }
        }

        void FreeAllDefPosVarNames(EAG.Alt A)
        {
            EAG.Factor F;

            void FreeVarNames(int P)
            {
                while (eag.ParamBuf[P].Affixform != EAG.nil)
                {
                    if (eag.ParamBuf[P].isDef)
                        Dispose(AffixName[P]);
                    ++P;
                }
            }

            F = A.Sub;
            while (F !is null)
            {
                if (auto nont = cast(EAG.Nont) F)
                    FreeVarNames(nont.Actual.Params);
                F = F.Next;
            }
            if (cast(EAG.Rep) Node)
                FreeVarNames(A.Actual.Params);
        }

        void InitComputation(EAG.ScopeDesc Scope)
        {
            trace!"RC: enter";
            InitScope(Scope);
            foreach (i; Scope.Beg .. Scope.End)
            {
                VarDeps[i] = VarCnt[i];
                if (eag.Var[i].Neg != EAG.nil)
                    ++VarDeps[i];
            }
        }

        void FinitComputation(EAG.ScopeDesc Scope)
        {
            trace!"RC: exit";
            foreach (i; Scope.Beg .. Scope.End)
            {
                VarRefCnt[i] = VarAppls[i];
                if (VarDepPos[i] >= 0)
                    ++VarRefCnt[i];
                trace!`RC: "%s" %s V%s (%s)`(eag.VarRepr(i), VarDeps[i], VarName[i], RefCnt[VarName[i]]);
            }
        }

        Prepare(N);
        trace!`RC: begin "%s": RefCnt=%s`(eag.HNontRepr(N), RefCnt[0 .. NextFreeVar + 1]);
        scope (exit)
            trace!`RC: end "%s": RefCnt=%s`(eag.HNontRepr(N), RefCnt[0 .. NextFreeVar + 1]);
        Node = eag.HNont[N].Def;
        isPred = eag.Pred[N];

        const Repetition = !isPred && cast(EAG.Rep) Node;
        int Dom = eag.HNont[N].Sig;

        while (eag.DomBuf[Dom] != EAG.nil)
        {
            if (FormalName[Dom] < 0)
                FormalName[Dom] = GetFreeVar;
            ++RefCnt[FormalName[Dom]];
            ++Dom;
        }
        if (Repetition)
        {
            Dom = eag.HNont[N].Sig;
            P = (cast(EAG.Rep) Node).Formal.Params;
            while (eag.DomBuf[Dom] != EAG.nil)
            {
                ActualName[Dom] = FormalName[Dom];
                if (!eag.ParamBuf[P].isDef)
                {
                    ActualName[Dom] = GetFreeVar;
                    ++RefCnt[ActualName[Dom]];
                }
                ++Dom;
                ++P;
            }
        }
        A = Node.Sub;
        do
        {
            InitComputation(A.Scope);
            trace!"RC: RefCnt=%s"(RefCnt[0 .. NextFreeVar + 1]);
            GetFormalParamNames(N, A.Formal.Params);
            if (Repetition)
            {
                Dom = eag.HNont[N].Sig;
                P = A.Actual.Params;
                while (eag.ParamBuf[P].Affixform != EAG.nil)
                {
                    if (eag.ParamBuf[P].isDef)
                    {
                        AffixName[P] = ActualName[Dom];
                        if (eag.ParamBuf[P].Affixform < 0)
                        {
                            VarName[-eag.ParamBuf[P].Affixform] = AffixName[P];
                            ++RefCnt[AffixName[P]];
                        }
                    }
                    ++P;
                    ++Dom;
                }
            }
            CheckDefPos(A.Formal.Params);
            F = A.Sub;
            while (F !is null)
            {
                if (auto nont = cast(EAG.Nont) F)
                {
                    GetActualParamNames(nont.Sym, nont.Actual.Params);
                    CheckApplPos(nont.Actual.Params, false);
                    if (embed && eag.Prod[nont.Sym] && !eag.Pred[nont.Sym] && eag.HNont[nont.Sym].anonymous)
                    {
                        Dom = eag.HNont[nont.Sym].Sig;
                        P = nont.Actual.Params;
                        while (eag.DomBuf[Dom] != EAG.nil)
                        {
                            FormalName[Dom] = AffixName[P];
                            ++Dom;
                            ++P;
                        }
                        Traverse(nont.Sym);
                    }
                    CheckDefPos(nont.Actual.Params);
                    FreeActualParamNames(nont.Actual.Params);
                }
                F = F.Next;
            }
            if (cast(EAG.Rep) Node)
            {
                GetActualParamNames(N, A.Actual.Params);
                CheckApplPos(A.Actual.Params, false);
                CheckDefPos(A.Actual.Params);
                FreeActualParamNames(A.Actual.Params);
            }
            CheckApplPos(A.Formal.Params, Repetition);
            if (isPred)
                FreeAllDefPosVarNames(A);
            FinitComputation(A.Scope);
            trace!"RC: RefCnt=%s"(RefCnt[0 .. NextFreeVar + 1]);
            A = A.Next;
        }
        while (A !is null);
        if (auto rep = cast(EAG.Rep) Node)
        {
            InitComputation(rep.Scope);
            GetFormalParamNames(N, rep.Formal.Params);
            CheckDefPos(rep.Formal.Params);
            CheckApplPos(rep.Formal.Params, true);
            FinitComputation(rep.Scope);
        }
        else if (auto opt = cast(EAG.Opt) Node)
        {
            InitComputation(opt.Scope);
            GetFormalParamNames(N, opt.Formal.Params);
            CheckDefPos(opt.Formal.Params);
            CheckApplPos(opt.Formal.Params, false);
            FinitComputation(opt.Scope);
        }
        if (Repetition)
        {
            P = (cast(EAG.Rep) Node).Formal.Params;
            while (eag.ParamBuf[P].Affixform != EAG.nil)
            {
                if (!eag.ParamBuf[P].isDef)
                    Dispose(AffixName[P]);
                ++P;
            }
        }
        Dom = eag.HNont[N].Sig;
        while (eag.DomBuf[Dom] != EAG.nil)
        {
            Dispose(FormalName[Dom]);
            ++Dom;
        }
    }

    void ComputeRepAppls(size_t N)
    {
        if (cast(EAG.Rep) eag.HNont[N].Def)
        {
            EAG.Alt A = eag.HNont[N].Def.Sub;

            do
            {
                foreach (param; A.Actual.params(eag))
                    if (param.isDef)
                        RepAppls[N] = RepAppls[N] && VarAppls[-param.Affixform] == 1;
                A = A.Next;
            }
            while (A !is null);
        }
    }

    FreeVar = new int[63];
    RefCnt = new int[63];
    ComputeRepAppls(N);
    NextFreeVar = 0;
    Top = 0;
    Traverse(N);
    HNontVars[N] = NextFreeVar;
    HNontDef[N] = true;
}

public void GenFormalParams(size_t N, Flag!"parNeeded" parNeeded)
{
    int Dom = eag.HNont[N].Sig;
    int i = 1;

    if (parNeeded)
        output.write("(");
    if (eag.DomBuf[Dom] != EAG.nil)
    {
        if (!parNeeded)
            output.write(", ");
        for (;;)
        {
            if (eag.DomBuf[Dom] > 0)
                output.write("ref ");
            output.write("HeapType ");
            GenVar(i);
            ++i;
            ++Dom;
            if (eag.DomBuf[Dom] == EAG.nil)
                break;
            output.write(", ");
        }
    }
    if (parNeeded)
        output.write(")");
    HNontFVars[N] = i;
}

public void GenVarDecl(size_t N)
{
    if (HNontVars[N] - HNontFVars[N] >= 0)
    {
        foreach (i; HNontFVars[N] .. HNontVars[N] + 1)
        {
            output.write("HeapType ");
            GenVar(i);
            output.writeln(";");
        }
    }
    if (eag.Pred[N])
        output.writeln("bool Failed;");
}

public void InitScope(EAG.ScopeDesc Scope) @nogc nothrow @safe
{
    foreach (i; Scope.Beg .. Scope.End)
        eag.Var[i].Def = false;
}

public void GenPredCall(int N, int ActualParams)
in (eag.Pred[N])
{
    output.write("Check", N, `("`);
    if (eag.HNont[N].anonymous)
        output.write("in ");
    output.write("'", eag.NamedHNontRepr(N), `'"`);
    GenActualParams(ActualParams, false);
    output.writeln(");");
}

public void GenActualParams(int P, bool ParNeeded) @safe
{
    if (ParNeeded)
        output.write("(");
    if (eag.ParamBuf[P].Affixform != EAG.nil)
    {
        if (!ParNeeded)
            output.write(", ");
        for (;;)
        {
            assert(AffixName[P] >= 0);

            GenVar(AffixName[P]);
            ++P;
            if (eag.ParamBuf[P].Affixform == EAG.nil)
                break;
            output.write(", ");
        }
    }
    if (ParNeeded)
        output.write(")");
}

public void GenSynPred(size_t Sym, int P)
{
    int Next;
    bool IsPred = eag.Pred[Sym];

    if (!UseRefCnt)
        GetAffixSpace(P);
    while (eag.ParamBuf[P].Affixform != EAG.nil)
    {
        if (!eag.ParamBuf[P].isDef)
        {
            const Tree = eag.ParamBuf[P].Affixform;

            if (SavePos)
                output.writeln("PopPos(", eag.MAlt[eag.NodeBuf[Tree]].Arity, ");");
            if (UseConst && AffixPlace[P] >= 0)
            {
                GenVar(AffixName[P]);
                output.writeln(" = ", AffixPlace[P], ";");
                if (UseRefCnt)
                    GenIncRefCnt(-AffixPlace[P], 1);
            }
            else if (Tree < 0)
            {
                const V = -Tree;

                if (UseRefCnt && IsPred)
                    GenIncRefCnt(VarName[V], 1);
                if (AffixName[P] != VarName[V])
                {
                    GenVar(AffixName[P]);
                    output.write(" = ");
                    GenVar(VarName[V]);
                    output.writeln(";");
                }
            }
            else
            {
                if (UseRefCnt)
                {
                    output.write("GetHeap(", eag.MAlt[eag.NodeBuf[Tree]].Arity, ", ");
                    GenVar(NodeName[Tree]);
                    output.write("); ");
                    Gen1SynTree(Tree, EmptySet, IsPred);
                    output.writeln;
                }
                else
                {
                    GenVar(AffixName[P]);
                    output.write(" = NextHeap; ");
                    Next = 0;
                    GenSynTree(Tree, EmptySet, Next);
                    GenHeapInc(Next);
                }
            }
        }
        ++P;
    }
}

private void GetAffixSpace(int P) @safe
{
    int Heap = 0;

    while (eag.ParamBuf[P].Affixform != EAG.nil)
    {
        if (!eag.ParamBuf[P].isDef && (!UseConst || UseConst && AffixPlace[P] < 0))
            Heap += AffixSpace[P];
        ++P;
    }
    GenOverflowGuard(Heap);
}

// RepVar is to be understood only in the context of generating repetition code
private void GenSynTree(int Node, BitArray RepVar, ref int Next)
{
    const Alt = eag.NodeBuf[Node];
    const Next1 = Next;

    GenHeap(0, Next);
    output.write(" = ", NodeIdent[Alt], "; ");
    Next += 1 + eag.MAlt[Alt].Arity;
    foreach (n; 0 .. eag.MAlt[Alt].Arity)
    {
        const Node1 = eag.NodeBuf[Node + n + 1];

        if (Node1 < 0)
        {
            const V = -Node1;

            if (RepVar[V])
            {
                GenVar(VarName[V]);
                output.write(" = NextHeap + ", Next1 + n + 1);
            }
            else
            {
                GenHeap(0, Next1 + n + 1);
                output.write(" = ");
                GenVar(VarName[V]);
            }
            output.write("; ");
        }
        else
        {
            GenHeap(0, Next1 + n + 1);
            output.write(" = ");
            if (UseConst && eag.MAlt[eag.NodeBuf[Node1]].Arity == 0)
            {
                output.write(Leaf[eag.NodeBuf[Node1]], "; ");
            }
            else
            {
                output.write("NextHeap + ", Next, "; ");
                GenSynTree(Node1, RepVar, Next);
            }
        }
    }
}

// RepVar is to be understood only in the context of generating repetition code
private void Gen1SynTree(int Node, BitArray RepVar, bool IsPred)
{
    GenHeap(NodeName[Node], 0);
    output.write(" = ", NodeIdent[eag.NodeBuf[Node]], "; ");
    foreach (n; 0 .. eag.MAlt[eag.NodeBuf[Node]].Arity)
    {
        const Node1 = eag.NodeBuf[Node + n + 1];

        if (Node1 < 0)
        {
            const V = -Node1;

            if (RepVar[V])
            {
                GenVar(VarName[V]);
                output.write(" = ");
                GenVar(NodeName[Node]);
                output.write(" + ", n + 1, "; ");
            }
            else
            {
                GenHeap(NodeName[Node], n + 1);
                output.write(" = ");
                GenVar(VarName[V]);
                output.write("; ");
                if (IsPred)
                    GenIncRefCnt(VarName[V], 1);
            }
        }
        else if (eag.MAlt[eag.NodeBuf[Node1]].Arity == 0)
        {
            if (UseConst)
            {
                GenHeap(NodeName[Node], n + 1);
                output.write(" = ", Leaf[eag.NodeBuf[Node1]], "; ");
                GenIncRefCnt(-Leaf[eag.NodeBuf[Node1]], 1);
            }
            else
            {
                output.write("GetHeap(0, ");
                GenHeap(NodeName[Node], n + 1);
                output.write("); Heap[");
                GenHeap(NodeName[Node], n + 1);
                output.write("] = ", NodeIdent[eag.NodeBuf[Node1]], ";");
            }
        }
        else
        {
            output.write("GetHeap(", eag.MAlt[eag.NodeBuf[Node1]].Arity, ", ");
            if (NodeName[Node] == NodeName[Node1])
            {
                GenHeap(NodeName[Node], n + 1);
                output.write("); ");
                GenVar(NodeName[Node1]);
                output.write(" = ");
                GenHeap(NodeName[Node], n + 1);
            }
            else
            {
                GenVar(NodeName[Node1]);
                output.write("); ");
                GenHeap(NodeName[Node], n + 1);
                output.write(" = ");
                GenVar(NodeName[Node1]);
            }
            output.writeln(";");
            Gen1SynTree(Node1, RepVar, IsPred);
        }
    }
}

public void GenAnalPred(size_t Sym, int P)
{
    bool MakeRefCnt;
    bool IsPred;

    void Comp()
    {
        if (UseRefCnt)
            output.write(".MOD(refConst)");
        output.write(IsPred ? " == " : " != ");
    }

    void GenEqualErrMsg(size_t Sym, int Var)
    {
        output.write(`"'`, eag.VarRepr(Var), "' failed in '", eag.NamedHNontRepr(Sym), `'"`);
    }

    void GenAnalErrMsg(size_t Sym)
    {
        output.write(`"`, eag.NamedHNontRepr(Sym), `"`);
    }

    void GenEqualPred(int VarName1, int Var2, bool Eq)
    {
        if (IsPred)
        {
            output.write("if (");
            if (!Eq)
                output.write("!");
            output.write("Equal(");
            GenVar(VarName1);
            output.write(", ");
            GenVar(VarName[Var2]);
            output.writeln("))");
            output.writeln("{");
            ++IfLevel;
        }
        else
        {
            if (!Eq)
                output.write("Un");
            output.write("Eq(");
            GenVar(VarName1);
            output.write(", ");
            GenVar(VarName[Var2]);
            output.write(", ");
            GenEqualErrMsg(Sym, Var2);
            output.write("); ");
        }
    }

    void GenAnalTree(int Node)
    {
        output.write("if (");
        GenHeap(NodeName[Node], 0);
        Comp;
        output.write(NodeIdent[eag.NodeBuf[Node]]);
        output.write(")");
        if (IsPred)
        {
            output.writeln;
            output.writeln("{");
            ++IfLevel;
        }
        else
        {
            output.write(" AnalyseError(");
            GenVar(NodeName[Node]);
            output.write(", ");
            GenAnalErrMsg(Sym);
            output.writeln(");");
        }
        foreach (n; 0 .. eag.MAlt[eag.NodeBuf[Node]].Arity)
        {
            const Node1 = eag.NodeBuf[Node + n + 1];

            if (Node1 < 0)
            {
                const V = -Node1;

                if (eag.Var[V].Def)
                {
                    if (IsPred)
                    {
                        output.write("if (Equal(");
                        GenHeap(NodeName[Node], n + 1);
                        output.write(", ");
                        GenVar(VarName[V]);
                        output.writeln("))");
                        output.writeln("{");
                        ++IfLevel;
                    }
                    else
                    {
                        output.write("Eq(");
                        GenHeap(NodeName[Node], n + 1);
                        output.write(", ");
                        GenVar(VarName[V]);
                        output.write(", ");
                        GenEqualErrMsg(Sym, V);
                        output.write("); ");
                    }
                }
                else
                {
                    eag.Var[V].Def = true;
                    GenVar(VarName[V]);
                    output.write(" = ");
                    GenHeap(NodeName[Node], n + 1);
                    output.write("; ");
                    if (eag.Var[eag.Var[V].Neg].Def)
                    {
                        const Vn = eag.Var[V].Neg;

                        GenEqualPred(VarName[Vn], V, false);
                        if (MakeRefCnt)
                        {
                            if (VarDepPos[Vn] == P)
                            {
                                GenFreeHeap(VarName[Vn]);
                                VarDepPos[Vn] = -2;
                            }
                        }
                    }
                    if (MakeRefCnt && VarRefCnt[V] > 0)
                        GenIncRefCnt(VarName[V], VarRefCnt[V]);
                }
                if (MakeRefCnt)
                {
                    if (VarDepPos[V] == P)
                    {
                        GenFreeHeap(VarName[V]);
                        VarDepPos[V] = -2;
                    }
                }
            }
            else
            {
                if (eag.MAlt[eag.NodeBuf[Node1]].Arity == 0)
                {
                    if (UseConst)
                    {
                        output.write("if (");
                        GenHeap(NodeName[Node], n + 1);
                        Comp;
                        output.write(Leaf[eag.NodeBuf[Node1]]);
                    }
                    else
                    {
                        output.write("if (Heap[");
                        GenHeap(NodeName[Node], n + 1);
                        output.write("]");
                        Comp;
                        output.write(NodeIdent[eag.NodeBuf[Node1]]);
                    }
                    output.write(")");
                    if (IsPred)
                    {
                        output.writeln;
                        output.writeln("{");
                        ++IfLevel;
                    }
                    else
                    {
                        output.write(" AnalyseError(");
                        GenHeap(NodeName[Node], n + 1);
                        output.write(", ");
                        GenAnalErrMsg(Sym);
                        output.write(");");
                    }
                    output.writeln;
                }
                else
                {
                    GenVar(NodeName[Node1]);
                    output.write(" = ");
                    GenHeap(NodeName[Node], n + 1);
                    output.write("; ");
                    GenAnalTree(Node1);
                }
            }
        }
    }

    IsPred = eag.Pred[Sym];
    IfLevel = 0;
    MakeRefCnt = UseRefCnt && !IsPred;
    while (eag.ParamBuf[P].Affixform != EAG.nil)
    {
        if (eag.ParamBuf[P].isDef)
        {
            const Tree = eag.ParamBuf[P].Affixform;

            if (Tree < 0)
            {
                const V = -Tree;

                if (eag.Var[V].Def)
                {
                    assert(AffixName[P] != VarName[V]);

                    GenEqualPred(AffixName[P], V, true);
                    if (MakeRefCnt)
                        GenFreeHeap(AffixName[P]);
                }
                else
                {
                    eag.Var[V].Def = true;
                    if (AffixName[P] != VarName[V])
                    {
                        GenVar(VarName[V]);
                        output.write(" = ");
                        GenVar(AffixName[P]);
                        output.writeln(";");
                    }
                    if (eag.Var[eag.Var[V].Neg].Def)
                    {
                        const Vn = eag.Var[V].Neg;

                        GenEqualPred(VarName[Vn], V, false);
                        if (MakeRefCnt)
                        {
                            if (VarDepPos[Vn] == P)
                            {
                                GenFreeHeap(VarName[Vn]);
                                VarDepPos[Vn] = -2;
                            }
                        }
                    }
                    if (MakeRefCnt)
                    {
                        if (VarRefCnt[V] > 1)
                            GenIncRefCnt(VarName[V], VarRefCnt[V] - 1);
                        else if (VarRefCnt[V] == 0)
                            GenFreeHeap(AffixName[P]);
                    }
                }
                if (MakeRefCnt)
                {
                    if (VarDepPos[V] == P)
                    {
                        GenFreeHeap(VarName[V]);
                        VarDepPos[V] = -2;
                    }
                }
            }
            else
            {
                if (eag.MAlt[eag.NodeBuf[Tree]].Arity == 0)
                {
                    output.write("if (");
                    GenHeap(AffixName[P], 0);
                    Comp;
                    output.write(NodeIdent[eag.NodeBuf[Tree]], ")");
                    if (IsPred)
                    {
                        output.writeln;
                        output.writeln("{");
                        ++IfLevel;
                    }
                    else
                    {
                        output.write(" AnalyseError(");
                        GenVar(AffixName[P]);
                        output.write(", ");
                        GenAnalErrMsg(Sym);
                        output.write(");");
                    }
                    output.writeln;
                }
                else
                {
                    GenAnalTree(Tree);
                }
                if (MakeRefCnt)
                    GenFreeHeap(AffixName[P]);
            }
        }
        ++P;
    }
    if (SavePos)
        output.writeln("PushPos;");
}

private void GenHeap(int Var, int Offset) @safe
{
    output.write("Heap[");
    if (Var <= 0)
        output.write("NextHeap");
    else
        GenVar(Var);
    if (Offset > 0)
    {
        output.write(" + ", Offset);
    }
    else if (Offset < 0)
    {
        output.write(" - ", -Offset);
    }
    output.write("]");
}

private void GenIncRefCnt(int Var, int n) @safe
{
    output.write("Heap[");
    if (Var < 0)
        output.write(-Var);
    else
        GenVar(Var);
    output.write("] += ");
    if (n != 1)
        output.write(n, " * ");
    output.writeln("refConst;");
}

private void GenOverflowGuard(int n) @safe
{
    if (n > 0)
    {
        output.writeln("if (NextHeap >= Heap.length - ", n, ")");
        output.writeln("EvalExpand;");
    }
}

private void GenFreeHeap(int Var) @safe
{
    output.write("FreeHeap(");
    GenVar(Var);
    output.writeln(");");
}

private void GenHeapInc(int n) @safe
{
    if (n != 0)
    {
        if (n == 1)
            output.writeln("++NextHeap;");
        else
            output.writeln("NextHeap += ", n, ";");
    }
}

private void GenVar(int Var) @safe
{
    output.write("V", Var);
}

static this() @nogc nothrow @safe
{
    Testing = false;
    Generating = false;
}

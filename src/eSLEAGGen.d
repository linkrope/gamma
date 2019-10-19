module eSLEAGGen;

import runtime;
import Sets = eSets;
import IO = eIO;
import EAG = eEAG;

const parsePass = 0;
const onePass = 1;
const sSweepPass = 2;
alias OpenInt = int[];
alias OpenBool = bool[];
IO.TextOut Mod;
IO.TextOut RC;
bool SavePos;
bool UseConst;
bool UseRefCnt;
bool TraversePass;
bool DebugRC;
OpenInt VarCnt;
OpenInt VarAppls;
bool Testing;
bool Generating;
Sets.OpenSet PreparedHNonts;
OpenInt VarDeps;
int FirstHeap;
OpenInt Leaf;
OpenInt MAltNum;
int MaxMAlt;
long RefConst;
OpenInt AffixPlace;
OpenInt AffixSpace;
OpenInt AffixName;
Sets.OpenSet HNontDef;
OpenInt HNontVars;
OpenInt HNontFVars;
OpenBool RepAppls;
OpenInt FormalName;
OpenInt VarRefCnt;
OpenInt VarDepPos;
OpenInt VarName;
OpenInt NodeName;
int IfLevel;
OpenInt ActualName;
Sets.OpenSet RepVar;
Sets.OpenSet EmptySet;

void InitScope(EAG.ScopeDesc Scope)
{
    int i;
    for (i = Scope.Beg; i <= Scope.End - 1; ++i)
    {
        EAG.Var[i].Def = false;
    }
}

void PrepareInit()
{
    NEW(VarCnt, EAG.NextVar);
    NEW(VarAppls, EAG.NextVar);
    Sets.New(RepVar, EAG.NextVar);
    Sets.New(PreparedHNonts, EAG.NextHNont);
}

void PrepareFinit()
{
    VarCnt = null;
    VarAppls = null;
    RepVar = null;
    PreparedHNonts = null;
}

void Prepare(int N)
{
    EAG.Rule Node;
    EAG.Alt A;
    EAG.Factor F;
    int P;

    void Traverse(int P)
    {
        void DefPos(int Node)
        {
            int n;
            if (Node < 0)
            {
                ++VarCnt[-Node];
            }
            else
            {
                for (n = 1; n <= EAG.MAlt[EAG.NodeBuf[Node]].Arity; ++n)
                {
                    DefPos(EAG.NodeBuf[Node + n]);
                }
            }
        }

        void ApplPos(int Node)
        {
            int n;
            if (Node < 0)
            {
                ++VarCnt[-Node];
                ++VarAppls[-Node];
            }
            else
            {
                for (n = 1; n <= EAG.MAlt[EAG.NodeBuf[Node]].Arity; ++n)
                {
                    ApplPos(EAG.NodeBuf[Node + n]);
                }
            }
        }

        while (EAG.ParamBuf[P].Affixform != EAG.nil)
        {
            if (EAG.ParamBuf[P].isDef)
            {
                DefPos(EAG.ParamBuf[P].Affixform);
            }
            else
            {
                ApplPos(EAG.ParamBuf[P].Affixform);
            }
            ++P;
        }
    }

    void InitArray(EAG.ScopeDesc Scope)
    {
        int i;
        for (i = Scope.Beg; i <= Scope.End - 1; ++i)
        {
            VarCnt[i] = 0;
            VarAppls[i] = 0;
        }
    }

    if (!Sets.In(PreparedHNonts, N))
    {
        Node = EAG.HNont[N].Def;
        if (Node is EAG.Rep)
        {
            InitArray(Node(EAG.Rep).Scope);
            Traverse(Node(EAG.Rep).Formal.Params);
        }
        else if (Node is EAG.Opt)
        {
            InitArray(Node(EAG.Opt).Scope);
            Traverse(Node(EAG.Opt).Formal.Params);
        }
        A = Node.Sub;
        do
        {
            InitArray(A.Scope);
            Traverse(A.Formal.Params);
            F = A.Sub;
            while (F !is null)
            {
                if (F is EAG.Nont)
                {
                    Traverse(F(EAG.Nont).Actual.Params);
                }
                F = F.Next;
            }
            if (Node is EAG.Rep)
            {
                Traverse(A.Actual.Params);
                P = A.Actual.Params;
                while (EAG.ParamBuf[P].Affixform != EAG.nil)
                {
                    if (EAG.ParamBuf[P].isDef && EAG.ParamBuf[P].Affixform < 0)
                    {
                        Sets.Incl(RepVar, -EAG.ParamBuf[P].Affixform);
                    }
                    ++P;
                }
            }
            A = A.Next;
        }
        while (A !is null);
        Sets.Incl(PreparedHNonts, N);
    }
}

bool TestHNont(int N, bool EmitErr, bool SLEAG)
{
    EAG.Rule Node;
    EAG.Alt A;
    EAG.Factor F;
    bool isSLEAG;
    bool isLEAG;
    int V;

    void Error(IO.Position Pos, string Msg)
    {
        isSLEAG = false;
        if (EmitErr)
        {
            IO.WriteText(IO.Msg, "\n\t");
            IO.WritePos(IO.Msg, Pos);
            IO.WriteText(IO.Msg, "\t");
            IO.WriteText(IO.Msg, Msg);
            IO.Update(IO.Msg);
        }
    }

    void CheckDefPos(int P)
    {
        void DefPos(int Node)
        {
            int n;
            int V;
            if (Node < 0)
            {
                V = -Node;
                if (!EAG.Var[V].Def)
                {
                    EAG.Var[V].Def = true;
                }
            }
            else
            {
                for (n = 1; n <= EAG.MAlt[EAG.NodeBuf[Node]].Arity; ++n)
                {
                    DefPos(EAG.NodeBuf[Node + n]);
                }
            }
        }

        while (EAG.ParamBuf[P].Affixform != EAG.nil)
        {
            if (EAG.ParamBuf[P].isDef)
            {
                DefPos(EAG.ParamBuf[P].Affixform);
            }
            ++P;
        }
    }

    void CheckApplPos(int P)
    {
        void ApplPos(int Node)
        {
            int n;
            int V;
            if (Node < 0)
            {
                V = -Node;
                if (!EAG.Var[V].Def)
                {
                    Error(EAG.Var[V].Pos, "not left-defining");
                    isLEAG = false;
                }
            }
            else
            {
                for (n = 1; n <= EAG.MAlt[EAG.NodeBuf[Node]].Arity; ++n)
                {
                    ApplPos(EAG.NodeBuf[Node + n]);
                }
            }
        }

        while (EAG.ParamBuf[P].Affixform != EAG.nil)
        {
            if (!EAG.ParamBuf[P].isDef)
            {
                ApplPos(EAG.ParamBuf[P].Affixform);
            }
            ++P;
        }
    }

    void CheckSLEAGCond(int P)
    {
        int Node;
        while (EAG.ParamBuf[P].Affixform != EAG.nil)
        {
            Node = EAG.ParamBuf[P].Affixform;
            if (EAG.ParamBuf[P].isDef)
            {
                if (Node >= 0)
                {
                    Error(EAG.ParamBuf[P].Pos, "Can't generate anal-predicate here");
                }
                else if (EAG.Var[-Node].Def)
                {
                    Error(EAG.ParamBuf[P].Pos, "Can't generate equal-predicate here");
                }
                else if (EAG.Var[EAG.Var[-Node].Neg].Def)
                {
                    Error(EAG.ParamBuf[P].Pos, "Can't generate unequal-predicate here");
                }
                else if (VarAppls[-Node] > 1)
                {
                    Error(EAG.ParamBuf[P].Pos, "Can't synthesize this variable several times");
                }
            }
            ++P;
        }
    }

    ASSERT(Sets.In(EAG.Prod, N), 98);
    isSLEAG = true;
    isLEAG = true;
    Prepare(N);
    Node = EAG.HNont[N].Def;
    if (Node is EAG.Rep)
    {
        InitScope(Node(EAG.Rep).Scope);
        CheckDefPos(Node(EAG.Rep).Formal.Params);
        CheckApplPos(Node(EAG.Rep).Formal.Params);
    }
    else if (Node is EAG.Opt)
    {
        InitScope(Node(EAG.Opt).Scope);
        CheckDefPos(Node(EAG.Opt).Formal.Params);
        CheckApplPos(Node(EAG.Opt).Formal.Params);
    }
    A = Node.Sub;
    do
    {
        InitScope(A.Scope);
        CheckDefPos(A.Formal.Params);
        F = A.Sub;
        while (F !is null)
        {
            if (F is EAG.Nont)
            {
                CheckApplPos(F(EAG.Nont).Actual.Params);
                if (SLEAG && EAG.HNont[F(EAG.Nont).Sym].Id < 0)
                {
                    isSLEAG = isSLEAG && TestHNont(F(EAG.Nont).Sym, EmitErr, SLEAG);
                }
                CheckDefPos(F(EAG.Nont).Actual.Params);
            }
            F = F.Next;
        }
        if (Node is EAG.Rep)
        {
            CheckApplPos(A.Actual.Params);
            if (SLEAG)
            {
                CheckSLEAGCond(A.Actual.Params);
            }
            CheckDefPos(A.Actual.Params);
        }
        CheckApplPos(A.Formal.Params);
        A = A.Next;
    }
    while (A !is null);
    if (SLEAG)
    {
        return isSLEAG;
    }
    else
    {
        return isLEAG;
    }
}

bool IsSLEAG(int N, bool EmitErr)
{
    return TestHNont(N, EmitErr, true);
}

bool IsLEAG(int N, bool EmitErr)
{
    return TestHNont(N, EmitErr, false);
}

void InitTest()
{
    if (!Generating && !Testing)
    {
        PrepareInit;
    }
    Testing = true;
}

void FinitTest()
{
    if (!Generating)
    {
        PrepareFinit;
    }
    Testing = false;
}

bool PredsOK()
{
    int N;
    bool OK;
    OK = true;
    for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
    {
        if (Sets.In(EAG.Pred, N))
        {
            OK = OK && IsLEAG(N, true);
        }
    }
    return OK;
}

void Test()
{
    int N;
    bool isSLEAG;
    bool isLEAG;
    IO.WriteString(IO.Msg, "SLEAG testing   ");
    IO.WriteString(IO.Msg, EAG.BaseName);
    IO.Update(IO.Msg);
    if (EAG.Performed(Set))
    {
        EXCL(EAG.History, EAG.isSLEAG);
        InitTest;
        isSLEAG = true;
        isLEAG = true;
        for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
        {
            if (Sets.In(EAG.Prod, N))
            {
                if (isSLEAG && EAG.HNont[N].Id >= 0)
                {
                    if (!TestHNont(N, true, true))
                    {
                        isSLEAG = false;
                        if (!TestHNont(N, false, false))
                        {
                            isLEAG = false;
                        }
                    }
                }
            }
        }
        if (isSLEAG)
        {
            INCL(EAG.History, EAG.isSLEAG);
            IO.WriteText(IO.Msg, "   ok");
        }
        else
        {
            if (isLEAG)
            {
                IO.WriteText(IO.Msg, "\n\tno SLEAG but LEAG");
            }
            else
            {
                IO.WriteText(IO.Msg, "\n\tno LEAG");
            }
        }
    }
    FinitTest;
    IO.WriteLn(IO.Msg);
    IO.Update(IO.Msg);
}

void GetMAltNum()
{
    int N;
    int A;
    int i;
    int temp;
    NEW(MAltNum, EAG.NextMAlt);
    for (A = EAG.firstMAlt; A <= EAG.NextMAlt - 1; ++A)
    {
        MAltNum[A] = -1;
    }
    MaxMAlt = 0;
    for (N = EAG.firstMNont; N <= EAG.NextMNont - 1; ++N)
    {
        A = EAG.MNont[N].MRule;
        i = 0;
        while (A != EAG.nil)
        {
            ++i;
            MAltNum[A] = i;
            A = EAG.MAlt[A].Next;
        }
        if (i > MaxMAlt)
        {
            MaxMAlt = i;
        }
    }
    i = 1;
    while (i <= MaxMAlt)
    {
        i = i * 2;
    }
    MaxMAlt = i;
    RefConst = 0;
    for (A = EAG.firstMAlt; A <= EAG.NextMAlt - 1; ++A)
    {
        ASSERT(MAltNum[A] >= 0, 89);
        temp = MAltNum[A] + EAG.MAlt[A].Arity * MaxMAlt;
        MAltNum[A] = temp;
        if (RefConst < MAltNum[A])
        {
            RefConst = MAltNum[A];
        }
    }
    i = 1;
    while (i <= RefConst)
    {
        i = i * 2;
    }
    RefConst = i;
}

void ComputeConstDat()
{
    int A;
    int i;
    int ConstPtr;

    void Traverse(int N, ref int ConstPtr)
    {
        EAG.Rule Node;
        EAG.Alt A;
        EAG.Factor F;
        void CheckParams(int P, ref int ConstPtr)
        {
            bool isConst;
            int Tree;
            void TraverseTree(int Node, ref int Next)
            {
                int n;
                int Arity;
                if (Node < 0)
                {
                    isConst = false;
                }
                else
                {
                    Arity = EAG.MAlt[EAG.NodeBuf[Node]].Arity;
                    if (!UseConst || Arity != 0)
                    {
                        INC(Next, 1 + Arity);
                    }
                    for (n = 1; n <= Arity; ++n)
                    {
                        TraverseTree(EAG.NodeBuf[Node + n], Next);
                    }
                }
            }

            while (EAG.ParamBuf[P].Affixform != EAG.nil)
            {
                Tree = EAG.ParamBuf[P].Affixform;
                isConst = true;
                TraverseTree(Tree, AffixSpace[P]);
                if (Tree > 0 && EAG.MAlt[EAG.NodeBuf[Tree]].Arity == 0)
                {
                    if (isConst)
                    {
                        AffixPlace[P] = Leaf[EAG.NodeBuf[Tree]];
                    }
                }
                else
                {
                    if (isConst)
                    {
                        AffixPlace[P] = ConstPtr;
                        INC(ConstPtr, AffixSpace[P]);
                    }
                }
                ++P;
            }
        }

        Node = EAG.HNont[N].Def;
        if (Node is EAG.Rep)
        {
            CheckParams(Node(EAG.Rep).Formal.Params, ConstPtr);
        }
        else if (Node is EAG.Opt)
        {
            CheckParams(Node(EAG.Opt).Formal.Params, ConstPtr);
        }
        A = Node.Sub;
        do
        {
            CheckParams(A.Formal.Params, ConstPtr);
            F = A.Sub;
            while (F !is null)
            {
                if (F is EAG.Nont)
                {
                    CheckParams(F(EAG.Nont).Actual.Params, ConstPtr);
                }
                F = F.Next;
            }
            if (Node is EAG.Rep)
            {
                CheckParams(A.Actual.Params, ConstPtr);
            }
            A = A.Next;
        }
        while (A !is null);
    }

    NEW(AffixSpace, EAG.NextParam);
    NEW(AffixPlace, EAG.NextParam);
    for (i = EAG.firstParam; i <= EAG.NextParam - 1; ++i)
    {
        AffixSpace[i] = 0;
        AffixPlace[i] = -1;
    }
    NEW(Leaf, EAG.NextMAlt);
    ConstPtr = EAG.MaxMArity + 1;
    FirstHeap = ConstPtr;
    for (A = EAG.firstMAlt; A <= EAG.NextMAlt - 1; ++A)
    {
        if (EAG.MAlt[A].Arity == 0)
        {
            Leaf[A] = ConstPtr;
            ++ConstPtr;
        }
        else
        {
            Leaf[A] = -1;
        }
    }
    for (i = EAG.firstHNont; i <= EAG.NextHNont - 1; ++i)
    {
        if (Sets.In(EAG.Prod, i))
        {
            Traverse(i, ConstPtr);
        }
    }
    if (UseConst)
    {
        FirstHeap = ConstPtr;
    }
}

void ComputeVarNames(int N, bool Embed)
{
    OpenInt FreeVar;
    OpenInt RefCnt;
    int Top;
    int NextFreeVar;
    int temp;

    void WriteRefCnt()
    {
        int i;
        IO.WriteText(RC, "WriteRefCnt: ");
        for (i = 0; i <= NextFreeVar; ++i)
        {
            IO.WriteInt(RC, RefCnt[i]);
            IO.WriteText(RC, ", ");
        }
        IO.WriteText(RC, " : \n");
    }

    void VarExpand()
    {
        OpenInt Int;
        int i;
        if (NextFreeVar >= RefCnt.length)
        {
            NEW(Int, 2 * RefCnt.length);
            for (i = 0; i <= NextFreeVar - 1; ++i)
            {
                Int[i] = RefCnt[i];
            }
            for (i = NextFreeVar; i <= SHORT(Int.length - 1); ++i)
            {
                Int[i] = 0;
            }
            RefCnt = Int;
        }
        if (Top >= FreeVar.length)
        {
            NEW(Int, 2 * FreeVar.length);
            for (i = 0; i <= Top - 1; ++i)
            {
                Int[i] = FreeVar[i];
            }
            FreeVar = Int;
        }
    }

    int GetFreeVar()
    {
        int Name;
        if (Top > 0)
        {
            --Top;
            Name = FreeVar[Top];
        }
        else
        {
            ++NextFreeVar;
            if (NextFreeVar >= RefCnt.length)
            {
                VarExpand;
            }
            RefCnt[NextFreeVar] = 0;
            Name = NextFreeVar;
        }
        if (DebugRC)
        {
            IO.WriteText(RC, " -");
            IO.WriteInt(RC, Name);
        }
        return Name;
    }

    void Dispose(int Var)
    {
        --RefCnt[Var];
        if (RefCnt[Var] == 0)
        {
            if (DebugRC)
            {
                IO.WriteText(RC, " +");
                IO.WriteInt(RC, Var);
            }
            FreeVar[Top] = Var;
            ++Top;
            if (Top >= FreeVar.length)
            {
                VarExpand;
            }
        }
    }

    void Traverse(int N)
    {
        EAG.Rule Node;
        EAG.Alt A;
        EAG.Factor F;
        int Dom;
        int P;
        int Tree;
        bool Repetition;
        bool isPred;

        void CheckDefPos(int P)
        {
            int Tree;
            int V;

            void DefPos(int Node, int Var)
            {
                int n;
                int Arity;
                int Node1;
                int Var1;
                int V;
                int Vn;
                bool NeedVar;
                if (Node < 0)
                {
                    V = -Node;
                    if (!EAG.Var[V].Def)
                    {
                        EAG.Var[V].Def = true;
                        if (VarName[V] < 0)
                        {
                            VarName[V] = GetFreeVar();
                            ++RefCnt[VarName[V]];
                        }
                        if (EAG.Var[EAG.Var[V].Neg].Def)
                        {
                            Vn = EAG.Var[V].Neg;
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
                        {
                            VarDepPos[V] = P;
                        }
                    }
                    --VarDeps[V];
                    if (VarDeps[V] == 0)
                    {
                        Dispose(VarName[V]);
                    }
                }
                else
                {
                    Arity = EAG.MAlt[EAG.NodeBuf[Node]].Arity;
                    if (Arity != 0)
                    {
                        NodeName[Node] = Var;
                    }
                    for (n = 1; n <= Arity; ++n)
                    {
                        Node1 = EAG.NodeBuf[Node + n];
                        NeedVar = ((isPred || UseRefCnt) && Var == AffixName[P] || n != Arity)
                            && Node1 >= 0 && EAG.MAlt[EAG.NodeBuf[Node1]].Arity > 0;
                        if (NeedVar)
                        {
                            Var1 = GetFreeVar();
                            ++RefCnt[Var1];
                        }
                        else
                        {
                            Var1 = Var;
                        }
                        DefPos(Node1, Var1);
                        if (NeedVar)
                        {
                            Dispose(Var1);
                        }
                    }
                }
            }

            while (EAG.ParamBuf[P].Affixform != EAG.nil)
            {
                Tree = EAG.ParamBuf[P].Affixform;
                if (EAG.ParamBuf[P].isDef)
                {
                    if (Tree < 0 && VarName[-Tree] < 0)
                    {
                        V = -Tree;
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
                int n;
                int Arity;
                int Node1;
                int Var1;
                int V;
                bool NeedVar;
                if (Node < 0)
                {
                    V = -Node;
                    --VarDeps[V];
                    if (VarDeps[V] == 0)
                    {
                        Dispose(VarName[V]);
                    }
                    if (VarDepPos[V] >= 0)
                    {
                        VarDepPos[V] = -1;
                    }
                }
                else
                {
                    Arity = EAG.MAlt[EAG.NodeBuf[Node]].Arity;
                    NodeName[Node] = Var;
                    for (n = 1; n <= Arity; ++n)
                    {
                        Node1 = EAG.NodeBuf[Node + n];
                        NeedVar = !(UseConst && AffixPlace[P] > 0) && UseRefCnt && (Var == AffixName[P]
                                || n != Arity) && Node1 >= 0
                            && EAG.MAlt[EAG.NodeBuf[Node1]].Arity > 0;
                        if (NeedVar)
                        {
                            Var1 = GetFreeVar();
                            ++RefCnt[Var1];
                        }
                        else
                        {
                            Var1 = Var;
                        }
                        ApplPos(Node1, Var1);
                        if (NeedVar)
                        {
                            Dispose(Var1);
                        }
                    }
                }
            }

            P1 = P;
            while (EAG.ParamBuf[P].Affixform != EAG.nil)
            {
                if (!EAG.ParamBuf[P].isDef)
                {
                    Tree = EAG.ParamBuf[P].Affixform;
                    if (Tree < 0 && VarName[-Tree] < 0)
                    {
                        V = -Tree;
                        VarName[V] = AffixName[P];
                        ++RefCnt[VarName[V]];
                    }
                    if (!(UseConst && AffixPlace[P] > 0) && Repetition && Tree >= 0)
                    {
                        NodeName[Tree] = GetFreeVar();
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
                while (EAG.ParamBuf[P1].Affixform != EAG.nil)
                {
                    if (!EAG.ParamBuf[P1].isDef && !(UseConst && AffixPlace[P1] > 0))
                    {
                        Tree = EAG.ParamBuf[P1].Affixform;
                        if (Tree >= 0)
                        {
                            Dispose(NodeName[Tree]);
                        }
                    }
                    ++P1;
                }
            }
        }

        void GetFormalParamNames(int N, int P)
        {
            bool Repetition;
            int Dom;
            int Tree;
            int V;
            Repetition = !Sets.In(EAG.Pred, N) && EAG.HNont[N].Def is EAG.Rep;
            Dom = EAG.HNont[N].Sig;
            while (EAG.ParamBuf[P].Affixform != EAG.nil)
            {
                if (Repetition)
                {
                    AffixName[P] = ActualName[Dom];
                }
                else
                {
                    AffixName[P] = FormalName[Dom];
                    Tree = EAG.ParamBuf[P].Affixform;
                    if (!EAG.ParamBuf[P].isDef && Tree < 0)
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

        void GetActualParamNames(int N, int P)
        {
            bool Repetition;
            int P1;
            int Tree;
            int V;

            int FindVarName(int P, int VarName)
            {
                while (AffixName[P] != VarName)
                {
                    ++P;
                }
                return P;
            }

            Repetition = !Sets.In(EAG.Pred, N) && EAG.HNont[N].Def is EAG.Rep;
            P1 = P;
            while (EAG.ParamBuf[P].Affixform != EAG.nil)
            {
                Tree = EAG.ParamBuf[P].Affixform;
                if (AffixName[P] < 0)
                {
                    if (Tree < 0 && VarName[-Tree] >= 0)
                    {
                        V = -Tree;
                        if (!EAG.ParamBuf[P].isDef)
                        {
                            if (Repetition && VarDeps[V] > 1)
                            {
                                AffixName[P] = GetFreeVar();
                            }
                            else if (!Sets.In(EAG.Pred, N) && EAG.HNont[N].Id < 0)
                            {
                                AffixName[P] = VarName[V];
                                if (FindVarName(P1, VarName[V]) != P)
                                {
                                    AffixName[P] = GetFreeVar();
                                }
                            }
                            else
                            {
                                AffixName[P] = VarName[V];
                            }
                        }
                        else
                        {
                            AffixName[P] = VarName[V];
                            if (EAG.Var[V].Def || FindVarName(P1, VarName[V]) != P)
                            {
                                AffixName[P] = GetFreeVar();
                            }
                        }
                    }
                    else
                    {
                        AffixName[P] = GetFreeVar();
                    }
                }
                ++RefCnt[AffixName[P]];
                if (isPred && EAG.ParamBuf[P].isDef)
                {
                    ++RefCnt[AffixName[P]];
                }
                ++P;
            }
        }

        void FreeActualParamNames(int P)
        {
            while (EAG.ParamBuf[P].Affixform != EAG.nil)
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
                while (EAG.ParamBuf[P].Affixform != EAG.nil)
                {
                    if (EAG.ParamBuf[P].isDef)
                    {
                        Dispose(AffixName[P]);
                    }
                    ++P;
                }
            }

            F = A.Sub;
            while (F !is null)
            {
                if (F is EAG.Nont)
                {
                    FreeVarNames(F(EAG.Nont).Actual.Params);
                }
                F = F.Next;
            }
            if (Node is EAG.Rep)
            {
                FreeVarNames(A.Actual.Params);
            }
        }

        void InitComputation(EAG.ScopeDesc Scope)
        {
            int i;
            InitScope(Scope);
            for (i = Scope.Beg; i <= Scope.End - 1; ++i)
            {
                VarDeps[i] = VarCnt[i];
                if (EAG.Var[i].Neg != EAG.nil)
                {
                    ++VarDeps[i];
                }
            }
            if (DebugRC)
            {
                IO.WriteText(RC, "\nOpen: ");
            }
        }

        void FinitComputation(EAG.ScopeDesc Scope)
        {
            int i;
            if (DebugRC)
            {
                IO.WriteText(RC, "\nClose: ");
            }
            for (i = Scope.Beg; i <= Scope.End - 1; ++i)
            {
                VarRefCnt[i] = VarAppls[i];
                if (VarDepPos[i] >= 0)
                {
                    ++VarRefCnt[i];
                }
                if (DebugRC)
                {
                    EAG.WriteVar(RC, i);
                    IO.Write(RC, " ");
                    IO.WriteInt(RC, VarDeps[i]);
                    IO.WriteString(RC, " V");
                    IO.WriteInt(RC, VarName[i]);
                    IO.WriteString(RC, " (");
                    IO.WriteInt(RC, RefCnt[VarName[i]]);
                    IO.WriteString(RC, "), ");
                }
            }
            if (DebugRC)
            {
                IO.WriteLn(RC);
            }
        }

        Prepare(N);
        if (DebugRC)
        {
            IO.WriteText(RC, "\nStart: ");
            EAG.WriteHNont(RC, N);
            IO.Write(RC, ":");
            WriteRefCnt;
        }
        Node = EAG.HNont[N].Def;
        isPred = Sets.In(EAG.Pred, N);
        Repetition = !isPred && Node is EAG.Rep;
        Dom = EAG.HNont[N].Sig;
        while (EAG.DomBuf[Dom] != EAG.nil)
        {
            if (FormalName[Dom] < 0)
            {
                FormalName[Dom] = GetFreeVar();
            }
            ++RefCnt[FormalName[Dom]];
            ++Dom;
        }
        if (Repetition)
        {
            Dom = EAG.HNont[N].Sig;
            P = Node(EAG.Rep).Formal.Params;
            while (EAG.DomBuf[Dom] != EAG.nil)
            {
                ActualName[Dom] = FormalName[Dom];
                if (!EAG.ParamBuf[P].isDef)
                {
                    ActualName[Dom] = GetFreeVar();
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
            if (DebugRC)
            {
                WriteRefCnt;
            }
            GetFormalParamNames(N, A.Formal.Params);
            if (Repetition)
            {
                Dom = EAG.HNont[N].Sig;
                P = A.Actual.Params;
                while (EAG.ParamBuf[P].Affixform != EAG.nil)
                {
                    if (EAG.ParamBuf[P].isDef)
                    {
                        AffixName[P] = ActualName[Dom];
                        if (EAG.ParamBuf[P].Affixform < 0)
                        {
                            VarName[-EAG.ParamBuf[P].Affixform] = AffixName[P];
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
                if (F is EAG.Nont)
                {
                    GetActualParamNames(F(EAG.Nont).Sym, F(EAG.Nont).Actual.Params);
                    CheckApplPos(F(EAG.Nont).Actual.Params, false);
                    if (Embed && Sets.In(EAG.Prod, F(EAG.Nont).Sym)
                            && !Sets.In(EAG.Pred, F(EAG.Nont).Sym)
                            && EAG.HNont[F(EAG.Nont).Sym].Id < 0)
                    {
                        Dom = EAG.HNont[F(EAG.Nont).Sym].Sig;
                        P = F(EAG.Nont).Actual.Params;
                        while (EAG.DomBuf[Dom] != EAG.nil)
                        {
                            FormalName[Dom] = AffixName[P];
                            ++Dom;
                            ++P;
                        }
                        Traverse(F(EAG.Nont).Sym);
                    }
                    CheckDefPos(F(EAG.Nont).Actual.Params);
                    FreeActualParamNames(F(EAG.Nont).Actual.Params);
                }
                F = F.Next;
            }
            if (Node is EAG.Rep)
            {
                GetActualParamNames(N, A.Actual.Params);
                CheckApplPos(A.Actual.Params, false);
                CheckDefPos(A.Actual.Params);
                FreeActualParamNames(A.Actual.Params);
            }
            CheckApplPos(A.Formal.Params, Repetition);
            if (isPred)
            {
                FreeAllDefPosVarNames(A);
            }
            FinitComputation(A.Scope);
            if (DebugRC)
            {
                WriteRefCnt;
            }
            A = A.Next;
        }
        while (A !is null);
        if (Node is EAG.Rep)
        {
            InitComputation(Node(EAG.Rep).Scope);
            GetFormalParamNames(N, Node(EAG.Rep).Formal.Params);
            CheckDefPos(Node(EAG.Rep).Formal.Params);
            CheckApplPos(Node(EAG.Rep).Formal.Params, true);
            FinitComputation(Node(EAG.Rep).Scope);
        }
        else if (Node is EAG.Opt)
        {
            InitComputation(Node(EAG.Opt).Scope);
            GetFormalParamNames(N, Node(EAG.Opt).Formal.Params);
            CheckDefPos(Node(EAG.Opt).Formal.Params);
            CheckApplPos(Node(EAG.Opt).Formal.Params, false);
            FinitComputation(Node(EAG.Opt).Scope);
        }
        if (Repetition)
        {
            P = Node(EAG.Rep).Formal.Params;
            while (EAG.ParamBuf[P].Affixform != EAG.nil)
            {
                if (!EAG.ParamBuf[P].isDef)
                {
                    Dispose(AffixName[P]);
                }
                ++P;
            }
        }
        Dom = EAG.HNont[N].Sig;
        while (EAG.DomBuf[Dom] != EAG.nil)
        {
            Dispose(FormalName[Dom]);
            ++Dom;
        }
        if (DebugRC)
        {
            IO.WriteText(RC, "\nEnde ");
            EAG.WriteHNont(RC, N);
            IO.WriteLn(RC);
            WriteRefCnt;
        }
    }

    void Bla(int N)
    {
        EAG.Alt A;
        int P;
        if (EAG.HNont[N].Def is EAG.Rep)
        {
            A = EAG.HNont[N].Def.Sub;
            do
            {
                P = A.Actual.Params;
                while (EAG.ParamBuf[P].Affixform != EAG.nil)
                {
                    if (EAG.ParamBuf[P].isDef)
                    {
                        RepAppls[N] = RepAppls[N] && VarAppls[-EAG.ParamBuf[P].Affixform] == 1;
                    }
                    ++P;
                }
                A = A.Next;
            }
            while (A !is null);
        }
    }

    ASSERT(Sets.In(EAG.Prod, N), 98);
    ASSERT(!Sets.In(HNontDef, N), 97);
    NEW(FreeVar, 63);
    NEW(RefCnt, 63);
    Bla(N);
    NextFreeVar = 0;
    Top = 0;
    Traverse(N);
    HNontVars[N] = NextFreeVar;
    Sets.Incl(HNontDef, N);
}

void InitGen(IO.TextOut MOut, int Treatment)
{
    bool isSLEAG;
    bool isLEAG;
    int i;
    int N;
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
        case sSweepPass:
            TraversePass = true;
            break;
        }
    }

    if (Generating)
    {
        IO.WriteText(IO.Msg, "\nresetting SLEAG\n");
        IO.Update(IO.Msg);
    }
    Mod = MOut;
    SavePos = false;
    TraversePass = false;
    UseConst = !IO.IsOption("c");
    UseRefCnt = !IO.IsOption("r");
    DebugRC = IO.IsLongOption("d", "R");
    SetFlags(Treatment);
    if (UseRefCnt)
    {
        IO.Write(IO.Msg, "+");
    }
    else
    {
        IO.Write(IO.Msg, "-");
    }
    IO.WriteString(IO.Msg, "rc ");
    if (UseConst)
    {
        IO.Write(IO.Msg, "+");
    }
    else
    {
        IO.Write(IO.Msg, "-");
    }
    IO.WriteString(IO.Msg, "ct ");
    IO.Update(IO.Msg);
    if (!Testing)
    {
        PrepareInit;
    }
    GetMAltNum;
    ComputeConstDat;
    if (DebugRC)
    {
        IO.CreateOut(RC, "Debug.RefCnt");
    }
    NEW(AffixName, EAG.NextParam);
    for (i = EAG.firstParam; i <= EAG.NextParam - 1; ++i)
    {
        AffixName[i] = -1;
    }
    NEW(NodeName, EAG.NextNode);
    NEW(VarName, EAG.NextVar);
    NEW(VarDeps, EAG.NextVar);
    NEW(VarRefCnt, EAG.NextVar);
    NEW(VarDepPos, EAG.NextVar);
    for (i = EAG.firstVar; i <= EAG.NextVar - 1; ++i)
    {
        VarRefCnt[i] = 0;
        VarDepPos[i] = -1;
        VarName[i] = -1;
    }
    NEW(ActualName, EAG.NextDom);
    NEW(FormalName, EAG.NextDom);
    for (i = EAG.firstDom; i <= EAG.NextDom - 1; ++i)
    {
        ActualName[i] = -1;
        FormalName[i] = -1;
    }
    NEW(HNontVars, EAG.NextHNont);
    NEW(HNontFVars, EAG.NextHNont);
    Sets.New(HNontDef, EAG.NextHNont);
    NEW(RepAppls, EAG.NextHNont);
    for (i = EAG.firstHNont; i <= EAG.NextHNont - 1; ++i)
    {
        RepAppls[i] = true;
    }
    Sets.New(EmptySet, EAG.NextVar);
    Generating = true;
}

void FinitGen()
{
    if (!Testing)
    {
        PrepareFinit;
    }
    EmptySet = null;
    MAltNum = null;
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
    if (DebugRC)
    {
        IO.Update(RC);
        IO.Show(RC);
    }
    Generating = false;
}

void Str(string s)
{
    IO.WriteText(Mod, s);
}

void Int(long i)
{
    IO.WriteInt(Mod, i);
}

void GenVar(int Var)
{
    Str("V");
    Int(Var);
}

void GenHeap(int Var, int Offset)
{
    Str("Heap[");
    if (Var <= 0)
    {
        Str("NextHeap");
    }
    else
    {
        GenVar(Var);
    }
    if (Offset > 0)
    {
        Str(" + ");
        Int(Offset);
    }
    else if (Offset < 0)
    {
        Str(" - ");
        Int(-Offset);
    }
    Str("]");
}

void GenIncRefCnt(int Var, int n)
{
    Str("INC(Heap[");
    if (Var < 0)
    {
        Int(-Var);
    }
    else
    {
        GenVar(Var);
    }
    Str("], ");
    if (n != 1)
    {
        Int(n);
        Str(" *");
    }
    Str(" refConst); \n");
}

void GenOverflowGuard(int n)
{
    if (n > 0)
    {
        Str("IF NextHeap >= LEN(Heap^) - ");
        Int(n);
        Str(" THEN EvalExpand END; \n");
    }
}

void GenFreeHeap(int Var)
{
    Str("FreeHeap(");
    GenVar(Var);
    Str("); \n");
}

void GenHeapInc(int n)
{
    if (n != 0)
    {
        if (n == 1)
        {
            Str("INC(NextHeap); \n");
        }
        else
        {
            Str("INC(NextHeap, ");
            Int(n);
            Str("); \n");
        }
    }
}

void GenDeclarations()
{
    IO.TextIn Fix;
    char[EAG.BaseNameLen + 10] Name;
    bool OpenError;
    long TabTimeStamp;

    void Append(ref string Dest, string Src, string Suf)
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
        while (Suf[j] != '\x00' && i < Dest.length - 1)
        {
            Dest[i] = Suf[j];
            ++i;
            ++j;
        }
        Dest[i] = '\x00';
    }

    void InclFix(char Term)
    {
        char c;
        IO.Read(Fix, c);
        while (c != Term)
        {
            if (c == '\x00')
            {
                IO.WriteText(IO.Msg, "\n\terror: unexpected end of eSLEAGGen.Fix\n");
                IO.Update(IO.Msg);
                HALT(99);
            }
            IO.Write(Mod, c);
            IO.Read(Fix, c);
        }
    }

    void SkipFix(char Term)
    {
        char c;
        IO.Read(Fix, c);
        while (c != Term)
        {
            if (c == '\x00')
            {
                IO.WriteText(IO.Msg, "\n\terror: unexpected end of eSLEAGGen.Fix\n");
                IO.Update(IO.Msg);
                HALT(99);
            }
            IO.Read(Fix, c);
        }
    }

    void GenTabFile(long TabTimeStamp)
    {
        const errVal = 0;
        const magic = 1818326597;
        int i;
        int P;
        int Next;
        int Start;
        IO.File Tab;
        int[] Heap;

        void SynTree(int Node, ref int Next)
        {
            int n;
            int Node1;
            int Next1;
            int Len1;
            Heap[Next] = MAltNum[EAG.NodeBuf[Node]];
            Next1 = Next;
            INC(Next, 1 + EAG.MAlt[EAG.NodeBuf[Node]].Arity);
            for (n = 1; n <= EAG.MAlt[EAG.NodeBuf[Node]].Arity; ++n)
            {
                Node1 = EAG.NodeBuf[Node + n];
                if (EAG.MAlt[EAG.NodeBuf[Node1]].Arity == 0)
                {
                    Heap[Next1 + n] = Leaf[EAG.NodeBuf[Node1]];
                }
                else
                {
                    Heap[Next1 + n] = Next;
                    SynTree(Node1, Next);
                }
            }
        }

        IO.CreateFile(Tab, Name);
        IO.PutLInt(Tab, magic);
        IO.PutLInt(Tab, TabTimeStamp);
        IO.PutLInt(Tab, FirstHeap - 1);
        NEW(Heap, FirstHeap);
        Heap[errVal] = 0;
        for (i = 1; i <= EAG.MaxMArity; ++i)
        {
            Heap[i] = errVal;
        }
        if (UseConst)
        {
            for (i = EAG.firstMAlt; i <= EAG.NextMAlt - 1; ++i)
            {
                if (Leaf[i] >= errVal)
                {
                    Heap[Leaf[i]] = MAltNum[i];
                }
            }
            for (P = EAG.firstParam; P <= EAG.NextParam - 1; ++P)
            {
                if (EAG.ParamBuf[P].Affixform != EAG.nil && AffixPlace[P] >= 0)
                {
                    Next = AffixPlace[P];
                    SynTree(EAG.ParamBuf[P].Affixform, Next);
                }
            }
        }
        for (i = 0; i <= FirstHeap - 1; ++i)
        {
            IO.PutLInt(Tab, Heap[i]);
        }
        IO.PutLInt(Tab, TabTimeStamp);
        IO.CloseFile(Tab);
    }

    if (TraversePass)
    {
        Append(Name, EAG.BaseName, "Eval.EvalTab");
    }
    else
    {
        Append(Name, EAG.BaseName, ".EvalTab");
    }
    TabTimeStamp = IO.TimeStamp();
    IO.OpenIn(Fix, "eSLEAGGen.Fix", OpenError);
    if (OpenError)
    {
        IO.WriteText(IO.Msg, "\n\terror: could not open eELL1Gen.Fix\n");
        IO.Update(IO.Msg);
        HALT(99);
    }
    InclFix("$");
    Int(FirstHeap - 1);
    InclFix("$");
    Int(MaxMAlt);
    InclFix("$");
    if (SavePos)
    {
        Str("Eval.TreeType");
    }
    else
    {
        Str("LONGINT");
    }
    InclFix("$");
    if (SavePos)
    {
        Str("Eval.OpenTree");
    }
    else
    {
        Str("POINTER TO ARRAY OF HeapType");
    }
    InclFix("$");
    if (SavePos)
    {
        InclFix("$");
    }
    else
    {
        SkipFix("$");
    }
    InclFix("$");
    Int(EAG.MaxMArity + 1);
    InclFix("$");
    Int(RefConst);
    InclFix("$");
    if (SavePos)
    {
        SkipFix("$");
        InclFix("$");
    }
    else
    {
        InclFix("$");
        SkipFix("$");
    }
    if (UseRefCnt)
    {
        InclFix("$");
        SkipFix("$");
    }
    else
    {
        SkipFix("$");
        InclFix("$");
    }
    InclFix("$");
    if (!TraversePass)
    {
        Str("S.");
    }
    InclFix("$");
    if (UseRefCnt)
    {
        InclFix("$");
    }
    else
    {
        SkipFix("$");
    }
    InclFix("$");
    Str(Name);
    InclFix("$");
    Int(TabTimeStamp);
    InclFix("$");
    if (SavePos)
    {
        InclFix("$");
    }
    else
    {
        SkipFix("$");
    }
    InclFix("$");
    GenTabFile(TabTimeStamp);
    IO.CloseIn(Fix);
}

bool PosNeeded(int P)
{
    int V;
    while (EAG.ParamBuf[P].Affixform != EAG.nil)
    {
        if (EAG.ParamBuf[P].isDef)
        {
            V = -EAG.ParamBuf[P].Affixform;
            if (V < 0)
            {
                return true;
            }
            else if (EAG.Var[V].Def)
            {
                return true;
            }
            else if (EAG.Var[EAG.Var[V].Neg].Def)
            {
                return true;
            }
        }
        ++P;
    }
    return false;
}

void GenAnalPred(int Sym, int P)
{
    int Node;
    int Tree;
    int n;
    int V;
    int Vn;
    bool MakeRefCnt;
    bool IsPred;

    void Comp()
    {
        if (UseRefCnt)
        {
            Str(" MOD refConst");
        }
        if (IsPred)
        {
            Str(" = ");
        }
        else
        {
            Str(" # ");
        }
    }

    void GenEqualErrMsg(int Sym, int Var)
    {
        Str("\''");
        EAG.WriteVar(Mod, Var);
        Str("' failed in '");
        EAG.WriteNamedHNont(Mod, Sym);
        Str("'\'");
    }

    void GenAnalErrMsg(int Sym)
    {
        Str("\"");
        EAG.WriteNamedHNont(Mod, Sym);
        Str("\"");
    }

    void GenEqualPred(int VarName1, int Var2, bool Eq)
    {
        if (IsPred)
        {
            Str("IF ");
            if (!Eq)
            {
                Str(" ~ ");
            }
            Str("Equal(");
            GenVar(VarName1);
            Str(", ");
            GenVar(VarName[Var2]);
            Str(") THEN \n");
            ++IfLevel;
        }
        else
        {
            if (!Eq)
            {
                Str("Un");
            }
            Str("Eq(");
            GenVar(VarName1);
            Str(", ");
            GenVar(VarName[Var2]);
            Str(", ");
            GenEqualErrMsg(Sym, Var2);
            Str("); ");
        }
    }

    void GenAnalTree(int Node)
    {
        int n;
        int Node1;
        int V;
        int Vn;
        Str("IF ");
        GenHeap(NodeName[Node], 0);
        Comp;
        Int(MAltNum[EAG.NodeBuf[Node]]);
        Str(" THEN ");
        if (IsPred)
        {
            Str("\n");
            ++IfLevel;
        }
        else
        {
            Str("AnalyseError(");
            GenVar(NodeName[Node]);
            Str(", ");
            GenAnalErrMsg(Sym);
            Str(") END; \n");
        }
        for (n = 1; n <= EAG.MAlt[EAG.NodeBuf[Node]].Arity; ++n)
        {
            Node1 = EAG.NodeBuf[Node + n];
            if (Node1 < 0)
            {
                V = -Node1;
                if (EAG.Var[V].Def)
                {
                    if (IsPred)
                    {
                        Str("IF Equal(");
                        GenHeap(NodeName[Node], n);
                        Str(", ");
                        GenVar(VarName[V]);
                        Str(") THEN \n");
                        ++IfLevel;
                    }
                    else
                    {
                        Str("Eq(");
                        GenHeap(NodeName[Node], n);
                        Str(", ");
                        GenVar(VarName[V]);
                        Str(", ");
                        GenEqualErrMsg(Sym, V);
                        Str("); ");
                    }
                }
                else
                {
                    EAG.Var[V].Def = true;
                    GenVar(VarName[V]);
                    Str(" := ");
                    GenHeap(NodeName[Node], n);
                    Str("; ");
                    if (EAG.Var[EAG.Var[V].Neg].Def)
                    {
                        Vn = EAG.Var[V].Neg;
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
                    {
                        GenIncRefCnt(VarName[V], VarRefCnt[V]);
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
                if (EAG.MAlt[EAG.NodeBuf[Node1]].Arity == 0)
                {
                    if (UseConst)
                    {
                        Str("IF ");
                        GenHeap(NodeName[Node], n);
                        Comp;
                        Int(Leaf[EAG.NodeBuf[Node1]]);
                    }
                    else
                    {
                        Str("IF Heap[");
                        GenHeap(NodeName[Node], n);
                        Str("]");
                        Comp;
                        Int(MAltNum[EAG.NodeBuf[Node1]]);
                    }
                    Str(" THEN ");
                    if (IsPred)
                    {
                        ++IfLevel;
                    }
                    else
                    {
                        IO.WriteString(Mod, "AnalyseError(");
                        GenHeap(NodeName[Node], n);
                        Str(", ");
                        GenAnalErrMsg(Sym);
                        IO.WriteString(Mod, ") END; ");
                    }
                    Str("\n");
                }
                else
                {
                    GenVar(NodeName[Node1]);
                    Str(" := ");
                    GenHeap(NodeName[Node], n);
                    Str("; ");
                    GenAnalTree(Node1);
                }
            }
        }
    }

    IsPred = Sets.In(EAG.Pred, Sym);
    IfLevel = 0;
    MakeRefCnt = UseRefCnt && !IsPred;
    while (EAG.ParamBuf[P].Affixform != EAG.nil)
    {
        if (EAG.ParamBuf[P].isDef)
        {
            Tree = EAG.ParamBuf[P].Affixform;
            if (Tree < 0)
            {
                V = -Tree;
                if (EAG.Var[V].Def)
                {
                    ASSERT(AffixName[P] != VarName[V]);
                    GenEqualPred(AffixName[P], V, true);
                    if (MakeRefCnt)
                    {
                        GenFreeHeap(AffixName[P]);
                    }
                }
                else
                {
                    EAG.Var[V].Def = true;
                    if (AffixName[P] != VarName[V])
                    {
                        GenVar(VarName[V]);
                        Str(" := ");
                        GenVar(AffixName[P]);
                        Str("; \n");
                    }
                    if (EAG.Var[EAG.Var[V].Neg].Def)
                    {
                        Vn = EAG.Var[V].Neg;
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
                        {
                            GenIncRefCnt(VarName[V], VarRefCnt[V] - 1);
                        }
                        else if (VarRefCnt[V] == 0)
                        {
                            GenFreeHeap(AffixName[P]);
                        }
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
                if (EAG.MAlt[EAG.NodeBuf[Tree]].Arity == 0)
                {
                    Str("IF ");
                    GenHeap(AffixName[P], 0);
                    Comp;
                    IO.WriteInt(Mod, MAltNum[EAG.NodeBuf[Tree]]);
                    Str(" THEN ");
                    if (IsPred)
                    {
                        ++IfLevel;
                    }
                    else
                    {
                        Str("AnalyseError(");
                        GenVar(AffixName[P]);
                        Str(", ");
                        GenAnalErrMsg(Sym);
                        Str(") END; ");
                    }
                    Str("\n");
                }
                else
                {
                    GenAnalTree(Tree);
                }
                if (MakeRefCnt)
                {
                    GenFreeHeap(AffixName[P]);
                }
            }
        }
        ++P;
    }
    if (SavePos)
    {
        Str("PushPos; \n");
    }
}
/**
 * RepVar ist nur im Kontext der Generierung von Repetition-Code zu verstehen
 */
void GenSynTree(int Node, Sets.OpenSet RepVar, ref int Next)
{
    int n;
    int Next1;
    int Node1;
    int V;
    int Alt;
    Alt = EAG.NodeBuf[Node];
    GenHeap(0, Next);
    Str(" := ");
    Int(MAltNum[Alt]);
    Str("; ");
    Next1 = Next;
    INC(Next, 1 + EAG.MAlt[Alt].Arity);
    for (n = 1; n <= EAG.MAlt[Alt].Arity; ++n)
    {
        Node1 = EAG.NodeBuf[Node + n];
        if (Node1 < 0)
        {
            V = -Node1;
            if (Sets.In(RepVar, V))
            {
                GenVar(VarName[V]);
                Str(" := NextHeap + ");
                Int(Next1 + n);
            }
            else
            {
                GenHeap(0, Next1 + n);
                Str(" := ");
                GenVar(VarName[V]);
            }
            Str("; ");
        }
        else
        {
            GenHeap(0, Next1 + n);
            Str(" := ");
            if (UseConst && EAG.MAlt[EAG.NodeBuf[Node1]].Arity == 0)
            {
                Int(Leaf[EAG.NodeBuf[Node1]]);
                Str("; ");
            }
            else
            {
                Str("NextHeap + ");
                Int(Next);
                Str("; ");
                GenSynTree(Node1, RepVar, Next);
            }
        }
    }
}
/**
 * RepVar ist nur im Kontext der Generierung von Repetition-Code zu verstehen
 */
void Gen1SynTree(int Node, Sets.OpenSet RepVar, bool IsPred)
{
    int n;
    int Node1;
    int V;
    GenHeap(NodeName[Node], 0);
    Str(" := ");
    Int(MAltNum[EAG.NodeBuf[Node]]);
    Str("; ");
    for (n = 1; n <= EAG.MAlt[EAG.NodeBuf[Node]].Arity; ++n)
    {
        Node1 = EAG.NodeBuf[Node + n];
        if (Node1 < 0)
        {
            V = -Node1;
            if (Sets.In(RepVar, V))
            {
                GenVar(VarName[V]);
                Str(" := ");
                GenVar(NodeName[Node]);
                Str(" + ");
                Int(n);
                Str("; ");
            }
            else
            {
                GenHeap(NodeName[Node], n);
                Str(" := ");
                GenVar(VarName[V]);
                Str("; ");
                if (IsPred)
                {
                    GenIncRefCnt(VarName[V], 1);
                }
            }
        }
        else if (EAG.MAlt[EAG.NodeBuf[Node1]].Arity == 0)
        {
            if (UseConst)
            {
                GenHeap(NodeName[Node], n);
                Str(" := ");
                Int(Leaf[EAG.NodeBuf[Node1]]);
                Str("; ");
                GenIncRefCnt(-Leaf[EAG.NodeBuf[Node1]], 1);
            }
            else
            {
                Str("GetHeap(0, ");
                GenHeap(NodeName[Node], n);
                Str("); Heap[");
                GenHeap(NodeName[Node], n);
                Str("] := ");
                Int(MAltNum[EAG.NodeBuf[Node1]]);
                Str("; ");
            }
        }
        else
        {
            Str("GetHeap(");
            Int(EAG.MAlt[EAG.NodeBuf[Node1]].Arity);
            Str(", ");
            if (NodeName[Node] == NodeName[Node1])
            {
                GenHeap(NodeName[Node], n);
                Str("); ");
                GenVar(NodeName[Node1]);
                Str(" := ");
                GenHeap(NodeName[Node], n);
            }
            else
            {
                GenVar(NodeName[Node1]);
                Str("); ");
                GenHeap(NodeName[Node], n);
                Str(" := ");
                GenVar(NodeName[Node1]);
            }
            Str("; \n");
            Gen1SynTree(Node1, RepVar, IsPred);
        }
    }
}

void GetAffixSpace(int P)
{
    int Heap;
    Heap = 0;
    while (EAG.ParamBuf[P].Affixform != EAG.nil)
    {
        if (!EAG.ParamBuf[P].isDef && (!UseConst || UseConst && AffixPlace[P] < 0))
        {
            INC(Heap, AffixSpace[P]);
        }
        ++P;
    }
    GenOverflowGuard(Heap);
}

void GenSynPred(int Sym, int P)
{
    int Next;
    int Tree;
    int n;
    int V;
    bool IsPred;
    IsPred = Sets.In(EAG.Pred, Sym);
    if (!UseRefCnt)
    {
        GetAffixSpace(P);
    }
    while (EAG.ParamBuf[P].Affixform != EAG.nil)
    {
        if (!EAG.ParamBuf[P].isDef)
        {
            Tree = EAG.ParamBuf[P].Affixform;
            if (SavePos)
            {
                Str("PopPos(");
                Int(EAG.MAlt[EAG.NodeBuf[Tree]].Arity);
                Str("); \n");
            }
            if (UseConst && AffixPlace[P] >= 0)
            {
                GenVar(AffixName[P]);
                Str(" := ");
                Int(AffixPlace[P]);
                Str("; \n");
                if (UseRefCnt)
                {
                    GenIncRefCnt(-AffixPlace[P], 1);
                }
            }
            else if (Tree < 0)
            {
                V = -Tree;
                if (UseRefCnt && IsPred)
                {
                    GenIncRefCnt(VarName[V], 1);
                }
                if (AffixName[P] != VarName[V])
                {
                    GenVar(AffixName[P]);
                    Str(" := ");
                    GenVar(VarName[V]);
                    Str(";\n");
                }
            }
            else
            {
                if (UseRefCnt)
                {
                    Str("GetHeap(");
                    Int(EAG.MAlt[EAG.NodeBuf[Tree]].Arity);
                    Str(", ");
                    GenVar(NodeName[Tree]);
                    Str("); ");
                    Gen1SynTree(Tree, EmptySet, IsPred);
                    Str("\n");
                }
                else
                {
                    GenVar(AffixName[P]);
                    Str(" := NextHeap; ");
                    Next = 0;
                    GenSynTree(Tree, EmptySet, Next);
                    GenHeapInc(Next);
                }
            }
        }
        ++P;
    }
}

void GenRepStart(int Sym)
{
    int P;
    int Dom;
    int Next;
    if (!UseRefCnt)
    {
        Next = 0;
        P = EAG.HNont[Sym].Def(EAG.Rep).Sub.Formal.Params;
        while (EAG.ParamBuf[P].Affixform != EAG.nil)
        {
            if (!EAG.ParamBuf[P].isDef)
            {
                ++Next;
            }
            ++P;
        }
        GenOverflowGuard(Next);
    }
    Dom = EAG.HNont[Sym].Sig;
    P = EAG.HNont[Sym].Def(EAG.Rep).Sub.Formal.Params;
    while (EAG.DomBuf[Dom] != EAG.nil)
    {
        if (!EAG.ParamBuf[P].isDef)
        {
            if (UseRefCnt)
            {
                Str("GetHeap(0, ");
                GenVar(FormalName[Dom]);
                Str("); ");
            }
            else
            {
                GenVar(FormalName[Dom]);
                Str(" := NextHeap; INC(NextHeap); ");
            }
            GenVar(AffixName[P]);
            Str(" := ");
            GenVar(FormalName[Dom]);
            Str("; \n");
        }
        ++P;
        ++Dom;
    }
}

void GenHangIn(int P, bool Guard)
{
    int Tree;
    int Next;

    void FreeVariables(int Node)
    {
        int n;
        if (Node < 0)
        {
            if (!Sets.In(RepVar, -Node))
            {
                Str("FreeHeap(");
                GenVar(VarName[-Node]);
                Str("); ");
            }
        }
        else
        {
            for (n = 1; n <= EAG.MAlt[EAG.NodeBuf[Node]].Arity; ++n)
            {
                FreeVariables(EAG.NodeBuf[Node + n]);
            }
        }
    }

    Next = 0;
    while (EAG.ParamBuf[P].Affixform != EAG.nil)
    {
        if (!EAG.ParamBuf[P].isDef)
        {
            Tree = EAG.ParamBuf[P].Affixform;
            if (Guard)
            {
                Str("IF ");
                GenVar(AffixName[P]);
                Str(" # undef THEN \n");
            }
            if (UseConst && AffixPlace[P] >= 0)
            {
                GenHeap(AffixName[P], 0);
                Str(" := ");
                Int(AffixPlace[P]);
                Str("; \n");
                if (UseRefCnt)
                {
                    GenIncRefCnt(-AffixPlace[P], 1);
                }
            }
            else if (Tree < 0)
            {
                if (AffixName[P] != VarName[-Tree])
                {
                    GenHeap(AffixName[P], 0);
                    Str(" := ");
                    GenVar(VarName[-Tree]);
                    Str("; \n");
                    if (Guard)
                    {
                        Str("ELSE FreeHeap(");
                        GenVar(VarName[-Tree]);
                        Str(") \n");
                    }
                }
            }
            else
            {
                if (UseRefCnt)
                {
                    Str("GetHeap(");
                    Int(EAG.MAlt[EAG.NodeBuf[Tree]].Arity);
                    Str(", ");
                    GenVar(NodeName[Tree]);
                    Str("); ");
                    GenHeap(AffixName[P], 0);
                    Str(" := ");
                    GenVar(NodeName[Tree]);
                    Str("; \n");
                    if (Guard)
                    {
                        Str("ELSE ");
                        FreeVariables(Tree);
                    }
                }
                else
                {
                    GenHeap(AffixName[P], 0);
                    Str(" := NextHeap");
                    if (Next != 0)
                    {
                        Str(" + ");
                        Int(Next);
                    }
                    Str("; \n");
                    INC(Next, AffixSpace[P]);
                    if (Guard)
                    {
                        Str("ELSE ");
                    }
                }
                if (Guard)
                {
                    GenVar(NodeName[Tree]);
                    Str(" := undef; \n");
                }
            }
            if (Guard)
            {
                Str("END; \n");
            }
        }
        ++P;
    }
}

void GenRepAlt(int Sym, EAG.Alt A)
{
    int P;
    int P1;
    int Dom;
    int Tree;
    int Next;
    bool Guard;
    Guard = !RepAppls[Sym];
    GenSynPred(Sym, A.Actual.Params);
    if (SavePos)
    {
        Str("PushPos; \n");
    }
    P = A.Actual.Params;
    Dom = EAG.HNont[Sym].Sig;
    while (EAG.ParamBuf[P].Affixform != EAG.nil)
    {
        if (!EAG.ParamBuf[P].isDef && AffixName[P] != FormalName[Dom])
        {
            GenVar(FormalName[Dom]);
            Str(" := ");
            GenVar(AffixName[P]);
            Str("; \n");
        }
        ++P;
        ++Dom;
    }
    P1 = A.Actual.Params;
    Dom = EAG.HNont[Sym].Sig;
    P = A.Formal.Params;
    if (!UseRefCnt)
    {
        GetAffixSpace(P);
    }
    GenHangIn(P, Guard);
    Next = 0;
    while (EAG.ParamBuf[P].Affixform != EAG.nil)
    {
        if (!EAG.ParamBuf[P].isDef)
        {
            Tree = EAG.ParamBuf[P].Affixform;
            if (SavePos)
            {
                Str("PopPos(");
                Int(EAG.MAlt[EAG.NodeBuf[Tree]].Arity);
                Str("); \n");
            }
            if (Tree > 0 && !(UseConst && AffixPlace[P] >= 0))
            {
                if (Guard)
                {
                    Str("IF ");
                    GenVar(NodeName[Tree]);
                    Str(" # undef THEN \n");
                }
                if (UseRefCnt)
                {
                    Gen1SynTree(Tree, RepVar, Sets.In(EAG.Pred, Sym));
                }
                else
                {
                    GenSynTree(Tree, RepVar, Next);
                }
                Str("\n");
                if (Guard)
                {
                    Str("END; \n");
                }
            }
            if (Guard && VarAppls[-EAG.ParamBuf[P1].Affixform] == 0)
            {
                GenVar(AffixName[P1]);
                Str(" := undef; \n");
            }
        }
        ++P;
        ++P1;
        ++Dom;
    }
    if (!UseRefCnt)
    {
        GenHeapInc(Next);
    }
}

void GenRepEnd(int Sym)
{
    int P;
    int P1;
    int Dom;
    int Tree;
    int Next;
    bool Guard;
    InitScope(EAG.HNont[Sym].Def(EAG.Rep).Scope);
    P = EAG.HNont[Sym].Def(EAG.Rep).Formal.Params;
    P1 = EAG.HNont[Sym].Def.Sub.Actual.Params;
    Dom = EAG.HNont[Sym].Sig;
    GenAnalPred(Sym, P);
    if (!UseRefCnt)
    {
        GetAffixSpace(P);
    }
    GenHangIn(P, Guard);
    Next = 0;
    while (EAG.ParamBuf[P].Affixform != EAG.nil)
    {
        if (!EAG.ParamBuf[P].isDef)
        {
            Tree = EAG.ParamBuf[P].Affixform;
            if (SavePos)
            {
                Str("PopPos(");
                Int(EAG.MAlt[EAG.NodeBuf[Tree]].Arity);
                Str("); \n");
            }
            if (Tree > 0 && !(UseConst && AffixPlace[P] >= 0))
            {
                if (Guard)
                {
                    Str("IF ");
                    GenVar(NodeName[Tree]);
                    Str(" # undef THEN \n");
                }
                if (UseRefCnt)
                {
                    Gen1SynTree(Tree, EmptySet, Sets.In(EAG.Pred, Sym));
                }
                else
                {
                    GenSynTree(Tree, EmptySet, Next);
                }
                Str("\n");
                if (Guard)
                {
                    Str("END; \n");
                }
            }
            if (UseRefCnt)
            {
                GenVar(AffixName[P]);
                Str(" := ");
                GenVar(FormalName[Dom]);
                Str("; ");
            }
            GenVar(FormalName[Dom]);
            Str(" := ");
            GenHeap(FormalName[Dom], 0);
            Str("; \n");
            if (UseRefCnt)
            {
                GenHeap(AffixName[P], 0);
                Str(" := 0; FreeHeap(");
                GenVar(AffixName[P]);
                Str("); \n");
            }
        }
        ++P;
        ++P1;
        ++Dom;
    }
    if (!UseRefCnt)
    {
        GenHeapInc(Next);
    }
}

void GenFormalParams(int N, bool ParNeeded)
{
    int Dom;
    int i;
    Dom = EAG.HNont[N].Sig;
    i = 1;
    if (ParNeeded)
    {
        Str("(");
    }
    if (EAG.DomBuf[Dom] != EAG.nil)
    {
        if (!ParNeeded)
        {
            Str("; ");
        }
        while (true)
        {
            if (EAG.DomBuf[Dom] > 0)
            {
                Str("VAR ");
            }
            GenVar(i);
            Str(": HeapType");
            ++i;
            ++Dom;
            if (EAG.DomBuf[Dom] == EAG.nil)
            {
                break;
            }
            Str("; ");
        }
    }
    if (ParNeeded)
    {
        Str(")");
        if (Sets.In(EAG.Pred, N))
        {
            Str(": BOOLEAN");
        }
    }
    HNontFVars[N] = i;
}

void GenVarDecl(int N)
{
    int i;
    if (HNontVars[N] - HNontFVars[N] >= 0)
    {
        Str("\tVAR ");
        for (i = HNontFVars[N]; i <= HNontVars[N]; ++i)
        {
            if (i != HNontFVars[N])
            {
                Str(", ");
            }
            GenVar(i);
        }
        Str(": HeapType;\n");
    }
    if (Sets.In(EAG.Pred, N))
    {
        Str("\tVAR Failed: BOOLEAN; \n");
    }
}

void GenActualParams(int P, bool ParNeeded)
{
    if (ParNeeded)
    {
        Str("(");
    }
    if (EAG.ParamBuf[P].Affixform != EAG.nil)
    {
        if (!ParNeeded)
        {
            Str(", ");
        }
        while (true)
        {
            ASSERT(AffixName[P] >= 0, 89);
            GenVar(AffixName[P]);
            ++P;
            if (EAG.ParamBuf[P].Affixform == EAG.nil)
            {
                break;
            }
            Str(", ");
        }
    }
    if (ParNeeded)
    {
        Str(")");
    }
}

void GenPredProcs()
{
    int N;

    void GenForward(int N)
    {
        void GenPredCover(int N)
        {
            int Dom;
            int i;
            ASSERT(Sets.In(EAG.Pred, N), 98);
            Str("PROCEDURE Check");
            Int(N);
            Str("(ErrMsg: ARRAY OF CHAR");
            GenFormalParams(N, false);
            Str("); \nBEGIN\n");
            Str("\tIF ~ Pred");
            Int(N);
            Str("(");
            Dom = EAG.HNont[N].Sig;
            i = 1;
            if (EAG.DomBuf[Dom] != EAG.nil)
            {
                while (true)
                {
                    GenVar(i);
                    ++Dom;
                    ++i;
                    if (EAG.DomBuf[Dom] == EAG.nil)
                    {
                        break;
                    }
                    Str(", ");
                }
            }
            Str(") THEN ");
            Dom = EAG.HNont[N].Sig;
            i = 1;
            while (EAG.DomBuf[Dom] > 0)
            {
                ++Dom;
            }
            if (EAG.DomBuf[Dom] != EAG.nil)
            {
                Str("IF (");
                while (true)
                {
                    GenVar(i);
                    Str(" # errVal) ");
                    do
                    {
                        ++Dom;
                        ++i;
                    }
                    while (!(EAG.DomBuf[Dom] <= 0));
                    if (EAG.DomBuf[Dom] == EAG.nil)
                    {
                        break;
                    }
                    Str("& (");
                }
                Str("THEN PredError(ErrMsg) END ");
            }
            else
            {
                Str("Error(ErrMsg) ");
            }
            Str("END \n");
            Str("END Check");
            Int(N);
            Str(";\n\n");
        }

        Str("PROCEDURE ^ Pred");
        Int(N);
        GenFormalParams(N, true);
        Str("; (* ");
        EAG.WriteHNont(Mod, N);
        Str(" *) \n\n");
        GenPredCover(N);
    }

    void GenPredicateCode(int N)
    {
        EAG.Rule Node;
        EAG.Alt A;
        EAG.ScopeDesc Scope;
        int P;
        int Level;
        int AltLevel;
        int i;
        void CleanLevel(int Level)
        {
            int i;
            if (Level >= 1)
            {
                for (i = 0; i <= Level - 1; ++i)
                {
                    Str("END ");
                }
                Str("; \n");
            }
        }

        void FreeParamTrees(int P)
        {
            while (EAG.ParamBuf[P].Affixform != EAG.nil)
            {
                if (EAG.ParamBuf[P].isDef)
                {
                    GenFreeHeap(AffixName[P]);
                }
                ++P;
            }
        }

        void TraverseFactor(EAG.Factor F, int FormalParams)
        {
            int Level;
            if (F !is null)
            {
                ASSERT(F is EAG.Nont, 99);
                ASSERT(Sets.In(EAG.Pred, F(EAG.Nont).Sym), 98);
                GenSynPred(N, F(EAG.Nont).Actual.Params);
                Str("\tIF Pred");
                Int(F(EAG.Nont).Sym);
                GenActualParams(F(EAG.Nont).Actual.Params, true);
                Str(" THEN (* ");
                EAG.WriteHNont(Mod, F(EAG.Nont).Sym);
                Str(" *) \n");
                GenAnalPred(N, F(EAG.Nont).Actual.Params);
                Level = IfLevel;
                TraverseFactor(F.Next, FormalParams);
                CleanLevel(Level);
                Str(" END; (* ");
                EAG.WriteHNont(Mod, F(EAG.Nont).Sym);
                Str(" *) \n");
                if (UseRefCnt)
                {
                    FreeParamTrees(F(EAG.Nont).Actual.Params);
                }
            }
            else
            {
                if (Node is EAG.Rep)
                {
                    GenSynPred(N, A.Actual.Params);
                    Str("\tIF Pred");
                    Int(N);
                    GenActualParams(A.Actual.Params, true);
                    Str(" THEN (* ");
                    EAG.WriteHNont(Mod, N);
                    Str(" *) \n");
                    GenAnalPred(N, A.Actual.Params);
                    Level = IfLevel;
                    GenSynPred(N, FormalParams);
                    Str("Failed := FALSE; \n");
                    CleanLevel(Level);
                    Str(" END; (* ");
                    EAG.WriteHNont(Mod, N);
                    Str(" *) \n");
                    if (UseRefCnt)
                    {
                        FreeParamTrees(A.Actual.Params);
                    }
                }
                else
                {
                    GenSynPred(N, FormalParams);
                    Str("Failed := FALSE; \n");
                }
            }
        }

        Node = EAG.HNont[N].Def;
        AltLevel = 0;
        Str("\tFailed := TRUE; \n");
        if (Node is EAG.Rep || Node is EAG.Opt)
        {
            if (Node is EAG.Opt)
            {
                P = Node(EAG.Opt).Formal.Params;
                Scope = Node(EAG.Opt).Scope;
            }
            else
            {
                P = Node(EAG.Rep).Formal.Params;
                Scope = Node(EAG.Rep).Scope;
            }
            InitScope(Scope);
            GenAnalPred(N, P);
            Level = IfLevel;
            GenSynPred(N, P);
            Str("Failed := FALSE; \n");
            CleanLevel(Level);
            ++AltLevel;
        }
        A = Node.Sub;
        while (true)
        {
            if (AltLevel > 0)
            {
                Str("IF Failed THEN (* ");
                Int(AltLevel + 1);
                Str(". Alternative *) \n");
            }
            InitScope(A.Scope);
            GenAnalPred(N, A.Formal.Params);
            Level = IfLevel;
            TraverseFactor(A.Sub, A.Formal.Params);
            CleanLevel(Level);
            ++AltLevel;
            A = A.Next;
            if (A is null)
            {
                break;
            }
        }
        for (i = 1; i <= AltLevel - 1; ++i)
        {
            Str("END ");
        }
        Str("; \n");
        P = Node.Sub.Formal.Params;
        if (UseRefCnt)
        {
            FreeParamTrees(P);
        }
        Str("IF Failed THEN ");
        while (EAG.ParamBuf[P].Affixform != EAG.nil)
        {
            if (!EAG.ParamBuf[P].isDef)
            {
                GenVar(AffixName[P]);
                Str(" := errVal; ");
                if (UseRefCnt)
                {
                    Str("INC(Heap[errVal], refConst); ");
                }
            }
            ++P;
        }
        Str(" END; \n");
    }

    for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
    {
        if (Sets.In(EAG.Pred, N))
        {
            GenForward(N);
        }
    }
    for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
    {
        if (Sets.In(EAG.Pred, N))
        {
            ComputeVarNames(N, false);
            Str("PROCEDURE Pred");
            Int(N);
            GenFormalParams(N, true);
            Str("; (* ");
            EAG.WriteHNont(Mod, N);
            Str(" *) \n");
            GenVarDecl(N);
            Str("BEGIN \n");
            GenPredicateCode(N);
            Str("RETURN ~ Failed\n");
            Str("END Pred");
            Int(N);
            Str("; \n\n");
        }
    }
}

void GenPredCall(int N, int ActualParams)
{
    ASSERT(Sets.In(EAG.Pred, N), 90);
    Str("\tCheck");
    Int(N);
    Str("(\'");
    if (EAG.HNont[N].Id < 0)
    {
        Str("in ");
    }
    Str("'");
    EAG.WriteNamedHNont(Mod, N);
    Str("'\'");
    GenActualParams(ActualParams, false);
    Str("); \n");
}

static this()
{
    Testing = false;
    Generating = false;
}

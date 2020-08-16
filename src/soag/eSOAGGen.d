module soag.eSOAGGen;

import runtime;
import EAG = eEAG;
import SOAG = soag.eSOAG;
import IO = eIO;
import Sets = eSets;
import SOAGPartition = soag.eSOAGPartition;
import SOAGVisitSeq = soag.eSOAGVisitSeq;
import SLEAGGen = eSLEAGGen;
import EmitGen = eEmitGen;
import SOAGOptimizer = soag.eSOAGOptimizer;
import Protocol = soag.eSOAGProtocol;

const cTab = 1;
const firstAffixOffset = 0;
const optimizedStorage = -1;
const notApplied = -2;
bool UseConst;
bool UseRefCnt;
bool Optimize;
SOAG.OpenInteger LocalVars;
SOAG.OpenInteger NodeName;
SOAG.OpenInteger AffixOffset;
SOAG.OpenInteger AffixVarCount;
SOAG.OpenInteger SubTreeOffset;
SOAG.OpenInteger FirstRule;
SOAG.OpenInteger AffixAppls;
IO.TextOut Out;
int Indent;
bool Error;
bool ShowMod;
bool Close;

/**
 * IN:  Regel
 * OUT: -
 * SEM: Berechnet im Feld NodeNames für alle Affixbaumanalysen der Regel
 *      die Namen der temp. Variablen für die Baumknoten;
 *      die maximale Variablenummer der Regel wird in LocalVars[] abgelegt
 */
void ComputeNodeNames(int R)
{
    int Var;
    int ProcVar;
    int AP;
    int AN;
    int Node;
    int SO;
    int V;
    int PBI;
    int AP1;
    int PBI1;
    int V1;
    bool sameAffix;

    /**
     * IN: Knoten in NodeBuf[], Variablenname
     * OUT: -
     * SEM: Berechnet für jeden Knoten des Teilbaums NodeBuf[Node]
     *      die temp. Variable für die Baumanalyse oder -synthese
     */
    void Traverse(int Node, ref int Var)
    {
        int Node1;
        int n;
        int Arity;
        Arity = EAG.MAlt[EAG.NodeBuf[Node]].Arity;
        ++Var;
        NodeName[Node] = Var;
        for (n = 1; n <= Arity; ++n)
        {
            Node1 = EAG.NodeBuf[Node + n];
            if (Node1 > 0)
            {
                if (UseConst && EAG.MAlt[EAG.NodeBuf[Node1]].Arity == 0)
                {
                    ++Var;
                    NodeName[Node1] = Var;
                }
                else
                {
                    Traverse(Node1, Var);
                }
            }
        }
    }

    LocalVars[R] = 0;
    for (AP = SOAG.Rule[R].AffOcc.Beg; AP <= SOAG.Rule[R].AffOcc.End; ++AP)
    {
        PBI = SOAG.AffOcc[AP].ParamBufInd;
        if (EAG.ParamBuf[PBI].isDef || UseRefCnt)
        {
            Var = 0;
            Node = EAG.ParamBuf[PBI].Affixform;
            if (Node > 0)
            {
                if (UseConst && EAG.MAlt[EAG.NodeBuf[Node]].Arity == 0)
                {
                    ++Var;
                    NodeName[Node] = Var;
                }
                else
                {
                    Traverse(Node, Var);
                }
            }
            if (Var > LocalVars[R])
            {
                LocalVars[R] = Var;
            }
        }
    }
    for (SO = SOAG.Rule[R].SymOcc.Beg; SO <= SOAG.Rule[R].SymOcc.End; ++SO)
    {
        if (SOAG.IsPredNont(SO))
        {
            Var = 0;
            ProcVar = 0;
            for (AP = SOAG.SymOcc[SO].AffOcc.Beg; AP <= SOAG.SymOcc[SO].AffOcc.End;
                    ++AP)
            {
                PBI = SOAG.AffOcc[AP].ParamBufInd;
                Node = EAG.ParamBuf[PBI].Affixform;
                if (!EAG.ParamBuf[PBI].isDef)
                {
                    if (Node > 0)
                    {
                        ++Var;
                        NodeName[Node] = Var;
                    }
                }
            }
            if (Var > LocalVars[R])
            {
                LocalVars[R] = Var;
            }
        }
    }
}

/**
 * IN:  Affixparameter
 * OUT: Affixposition
 * SEM: gibt die Affixposition zurück, zu der der Affixparameter korrespondiert
 */
int GetCorrespondedAffPos(int AP)
{
    int SO;
    int AN;
    SO = SOAG.AffOcc[AP].SymOccInd;
    AN = AP - SOAG.SymOcc[SO].AffOcc.Beg;
    return SOAG.Sym[SOAG.SymOcc[SO].SymInd].AffPos.Beg + AN;
}

void WrAffixAppls(int R)
{
    EAG.ScopeDesc Scope;
    EAG.Rule EAGRule;
    int V;
    if (cast(SOAG.OrdRule) SOAG.Rule[R] !is null)
    {
        Scope = (cast(SOAG.OrdRule) SOAG.Rule[R]).Alt.Scope;
    }
    else
    {
        EAGRule = (cast(SOAG.EmptyRule) SOAG.Rule[R]).Rule;
        if (cast(EAG.Opt) EAGRule !is null)
        {
            Scope = (cast(EAG.Opt) EAGRule).Scope;
        }
        else if (cast(EAG.Rep) EAGRule !is null)
        {
            Scope = (cast(EAG.Rep) EAGRule).Scope;
        }
    }
    for (V = Scope.Beg; V <= Scope.End - 1; ++V)
    {
        EAG.WriteVar(IO.Msg, V);
        IO.WriteText(IO.Msg, ": ");
        IO.WriteInt(IO.Msg, AffixAppls[V]);
        IO.WriteLn(IO.Msg);
        IO.Update(IO.Msg);
    }
}

/**
 * IN:  Regel
 * OUT: -
 * SEM: berechnet im Feld AffixOffset[], das parallel zu EAG.Var liegt,
 *      den Offset der Affixvariablen im Feld Var[] des generierten Compilers;
 *      alle nicht-applizierten Affixvariablen (AffixAppls[]=0) werden ausgelassen
 * PRE: AffixAppls[] muss berechnet sein
 */
void ComputeAffixOffset(int R)
{
    EAG.ScopeDesc Scope;
    EAG.Rule EAGRule;
    int A;
    int AP;
    int Offset;
    if (cast(SOAG.OrdRule) SOAG.Rule[R] !is null)
    {
        Scope = (cast(SOAG.OrdRule) SOAG.Rule[R]).Alt.Scope;
    }
    else
    {
        EAGRule = (cast(SOAG.EmptyRule) SOAG.Rule[R]).Rule;
        if (cast(EAG.Opt) EAGRule !is null)
        {
            Scope = (cast(EAG.Opt) EAGRule).Scope;
        }
        else if (cast(EAG.Rep) EAGRule !is null)
        {
            Scope = (cast(EAG.Rep) EAGRule).Scope;
        }
    }
    Offset = firstAffixOffset;
    for (A = Scope.Beg; A <= Scope.End - 1; ++A)
    {
        if (AffixAppls[A] > 0)
        {
            if (Optimize)
            {
                AP = GetCorrespondedAffPos(SOAG.DefAffOcc[A]);
                if (SOAG.StorageName[AP] == 0)
                {
                    AffixOffset[A] = Offset;
                    ++Offset;
                }
                else
                {
                    AffixOffset[A] = optimizedStorage;
                }
            }
            else
            {
                AffixOffset[A] = Offset;
                ++Offset;
            }
        }
        else
        {
            AffixOffset[A] = notApplied;
        }
    }
    AffixVarCount[R] = Offset - firstAffixOffset;
}

/**
 * SEM: liefert die echte Anzahl an Affixvariablen in der Regel;
 *      nur zur Information über die Optimierungleistung
 */
int GetAffixCount(int R)
{
    EAG.ScopeDesc Scope;
    EAG.Rule EAGRule;
    if (cast(SOAG.OrdRule) SOAG.Rule[R] !is null)
    {
        Scope = (cast(SOAG.OrdRule) SOAG.Rule[R]).Alt.Scope;
    }
    else
    {
        EAGRule = (cast(SOAG.EmptyRule) SOAG.Rule[R]).Rule;
        if (cast(EAG.Opt) EAGRule !is null)
        {
            Scope = (cast(EAG.Opt) EAGRule).Scope;
        }
        else if (cast(EAG.Rep) EAGRule !is null)
        {
            Scope = (cast(EAG.Rep) EAGRule).Scope;
        }
    }
    return Scope.End - Scope.Beg;
}

/**
 * IN:  -
 * OUT: Hyper-Arity-Konstante
 * SEM: Liefert die Arity-Konstante für den Ableitungsbaum, der durch den Parser erzeugt wird;
 *      müsste eigentlich von SLEAG geliefert werden (in SSweep wurde es auch intern definiert,
 *      deshalb wird es hier für spätere Module exportiert)
 */
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

/**
 * SEM: Initialisierung der Datenstrukturen des Moduls
 */
void Init()
{
    int i;
    int R;
    int SO;
    int S;
    int Offset;
    int len;
    int POI;
    NEW(LocalVars, SOAG.NextRule);
    NEW(AffixVarCount, SOAG.NextRule);
    NEW(AffixOffset, EAG.NextVar);
    NEW(NodeName, EAG.NextNode);
    NEW(SubTreeOffset, SOAG.NextSymOcc);
    NEW(FirstRule, SOAG.NextSym);
    NEW(AffixAppls, EAG.NextVar);
    for (i = SOAG.firstRule; i <= SOAG.NextRule - 1; ++i)
    {
        LocalVars[i] = 0;
        AffixVarCount[i] = -1;
    }
    for (i = EAG.firstNode; i <= EAG.NextNode - 1; ++i)
    {
        NodeName[i] = -1;
    }
    for (i = EAG.firstVar; i <= EAG.NextVar - 1; ++i)
    {
        EAG.Var[i].Def = false;
        AffixAppls[i] = SOAG.AffixApplCnt[i];
    }
    for (R = SOAG.firstRule; R <= SOAG.NextRule - 1; ++R)
    {
        Offset = 0;
        for (SO = SOAG.Rule[R].SymOcc.Beg + 1; SO <= SOAG.Rule[R].SymOcc.End; ++SO)
        {
            if (!SOAG.IsPredNont(SO))
            {
                ++Offset;
                SubTreeOffset[SO] = Offset;
            }
        }
    }
    for (S = SOAG.firstSym; S <= SOAG.NextSym - 1; ++S)
    {
        SO = SOAG.Sym[S].FirstOcc;
        if (SO != SOAG.nil)
        {
            R = SOAG.SymOcc[SO].RuleInd;
            while (SO != SOAG.Rule[R].SymOcc.Beg)
            {
                SO = SOAG.SymOcc[SO].Next;
                R = SOAG.SymOcc[SO].RuleInd;
            }
            SO = SOAG.SymOcc[SO].Next;
            while (R >= SOAG.firstRule && S == SOAG.SymOcc[SOAG.Rule[R].SymOcc.Beg].SymInd)
            {
                FirstRule[S] = R;
                --R;
            }
        }
    }
}

void Ind()
{
    int i;
    for (i = 1; i <= Indent; ++i)
    {
        IO.WriteText(Out, "    ");
    }
}

void WrS(T)(T String)
{
    IO.WriteText(Out, String);
}

void WrI(int Int)
{
    IO.WriteInt(Out, Int);
}

void WrSI(string String, int Int)
{
    IO.WriteText(Out, String);
    IO.WriteInt(Out, Int);
}

void WrIS(int Int, string String)
{
    IO.WriteInt(Out, Int);
    IO.WriteText(Out, String);
}

void WrSIS(string String1, int Int, string String2)
{
    IO.WriteText(Out, String1);
    IO.WriteInt(Out, Int);
    IO.WriteText(Out, String2);
}

void GenHeapInc(int n)
{
    if (n != 0)
    {
        if (n == 1)
        {
            WrS("INC(NextHeap); \n");
        }
        else
        {
            WrSIS("INC(NextHeap, ", n, "); \n");
        }
    }
}

void GenVar(int Var)
{
    WrSI("V", Var);
}

void GenHeap(int Var, int Offset)
{
    WrS("Heap[");
    if (Var > 0)
    {
        GenVar(Var);
    }
    else
    {
        WrS("NextHeap");
    }
    if (Offset > 0)
    {
        WrSI(" + ", Offset);
    }
    else if (Offset < 0)
    {
        WrSI(" - ", -Offset);
    }
    WrS("]");
}

void GenOverflowGuard(int n)
{
    if (n > 0)
    {
        WrSIS("if (NextHeap >= Heap.length - ", n, ") EvalExpand;\n");
    }
}

/**
 * IN:  Symbol, Nummer eines Affixparameter relativ zum Symbolvorkommen
 * OUT: -
 * SEM: Generierung eines Zugriffs auf die Instanz einer Affixposition
 */
void GenAffPos(int S, int AN)
{
    int SN;
    int AP;
    WrSIS("AffPos[S", S, " + ");
    WrIS(AN, "]");
}

/**
 * IN: Affixnummer
 * OUT: -
 * SEM: Generiert einen Zugriff auf den Inhalt eines Affixes
 */
void GenAffix(int V)
{
    int AP;
    ASSERT(AffixOffset[V] != notApplied);
    if (AffixOffset[V] == optimizedStorage)
    {
        AP = GetCorrespondedAffPos(SOAG.DefAffOcc[V]);
        if (SOAG.StorageName[AP] > 0)
        {
            WrSIS("Stacks.Top(Stack", SOAG.StorageName[AP], ") ");
        }
        else
        {
            WrSI("GV", -SOAG.StorageName[AP]);
        }
    }
    else
    {
        WrSIS("Var[VI + ", AffixOffset[V], "]");
    }
}

/**
 * IN: Affix
 * OUT: -
 * SEM: Generierung einer Zuweisung zu einer Instanz einer Affixvariable;
 *      nur in Kombination mit der Prozedur GenClose zu verwenden
 */
void GenAffixAssign(int V)
{
    int AP;
    ASSERT(AffixOffset[V] != notApplied);
    if (AffixOffset[V] == optimizedStorage)
    {
        AP = GetCorrespondedAffPos(SOAG.DefAffOcc[V]);
        if (SOAG.StorageName[AP] > 0)
        {
            WrSIS("Stacks.Push(Stack", SOAG.StorageName[AP], ", ");
            Close = true;
        }
        else
        {
            WrSIS("GV", -SOAG.StorageName[AP], " = ");
            Close = false;
        }
    }
    else
    {
        WrSIS("Var[VI + ", AffixOffset[V], "] = ");
        Close = false;
    }
}

void GenClose()
{
    if (Close)
    {
        WrS("); ");
    }
    else
    {
        WrS("; ");
    }
}

/**
 * IN: Affixvariable oder (< 0) lokale Variable
 * OUT: -
 * SEM: Generiert eine Erhöhung des Referenzzählers des Knotens auf den das Affixes
 *      bzw. der Index verweist, im Falle eines Stacks wird globale Var. RefIncVar verwendet
 */
void GenIncRefCnt(int Var)
{
    int AP;
    WrS("INC(Heap[");
    if (Var < 0)
    {
        GenVar(-Var);
    }
    else
    {
        GenAffix(Var);
    }
    WrS("], refConst);\n");
}

/**
 * IN: Affixvariable
 * OUT: -
 * SEM: generiert die Freigabe des alloziierten Speichers,
 *      wenn die Affixvariable das letzte mal appliziert wurde (AffixAppls = 0)
 */
void GenFreeAffix(int V)
{
    int AP;
    if (AffixAppls[V] == 0)
    {
        Ind;
        WrS("FreeHeap(");
        GenAffix(V);
        WrS(");\n");
    }
}

/**
 * IN: Affixvariable
 * OUT: -
 * SEM: generiert die Kellerspeicherfreigabe,
 *      wenn die Affixvariable das letzte mal appliziert wurde (AffixAppls = 0)
 */
void GenPopAffix(int V)
{
    int AP;
    if (AffixAppls[V] == 0)
    {
        if (AffixOffset[V] == optimizedStorage)
        {
            AP = GetCorrespondedAffPos(SOAG.DefAffOcc[V]);
            if (SOAG.StorageName[AP] > 0)
            {
                Ind;
                WrSIS("Stacks.Pop(Stack", SOAG.StorageName[AP], ");\n");
            }
            else
            {
                Ind;
                WrSIS("GV", -SOAG.StorageName[AP], " = -1;\n");
            }
        }
    }
}

/**
 * IN: Symbolvorkommen
 * OUT: -
 * SEM: Generierung der Syntheseaktionen eines Besuchs für die besuchsrelevanten Affixparameter eines Symbolvorkommens
 */
void GenSynPred(int SymOccInd, int VisitNo)
{
    int Node;
    int S;
    int Offset;
    int AP;
    int AN;
    int V;
    int SN;
    int P;
    bool IsPred;

    /**
     * IN: Knoten des Affixbaumes, Offset des nächsten freien Heap-Elementes
     * OUT: -
     * SEM: Traversierung eines Affixbaumes und Ausgabe der Syntheseaktionen für den zu generierenden Compiler
     */
    void GenSynTraverse(int Node, ref int Offset)
    {
        int Offset1;
        int Node1;
        int n;
        int V;
        int Alt;
        Alt = EAG.NodeBuf[Node];
        Ind;
        GenHeap(-1, Offset);
        WrSIS(" = ", SLEAGGen.NodeIdent[Alt], ";\n");
        Offset1 = Offset;
        INC(Offset, 1 + EAG.MAlt[Alt].Arity);
        for (n = 1; n <= EAG.MAlt[Alt].Arity; ++n)
        {
            Node1 = EAG.NodeBuf[Node + n];
            if (Node1 < 0)
            {
                V = -Node1;
                if (!EAG.Var[V].Def)
                {
                    SOAG.Error(SOAG.abnormalyError, "eSOAGGen.GenSynTraverse: Affix nicht definiert.");
                }
                else
                {
                    Ind;
                    GenHeap(-1, Offset1 + n);
                    WrS(" = ");
                    GenAffix(V);
                    WrS(";\n");
                    --AffixAppls[V];
                    if (UseRefCnt)
                    {
                        GenFreeAffix(V);
                    }
                    if (Optimize)
                    {
                        GenPopAffix(V);
                    }
                }
            }
            else
            {
                Ind;
                GenHeap(-1, Offset1 + n);
                WrS(" = ");
                if (UseConst && EAG.MAlt[EAG.NodeBuf[Node1]].Arity == 0)
                {
                    WrIS(SLEAGGen.Leaf[EAG.NodeBuf[Node1]], ";\n");
                }
                else
                {
                    WrSIS("NextHeap + ", Offset, ";\n");
                    GenSynTraverse(Node1, Offset);
                }
            }
        }
    }

    /**
     * IN: Knoten des Affixbaumes
     * OUT: -
     * SEM: Traversierung eines Affixbaumes und Ausgabe der Syntheseaktionen mit Referenzzähler-Verfahren
     *      für den zu generierenden Compiler
     */
    void GenSynTraverseRefCnt(int Node)
    {
        int Node1;
        int n;
        int V;
        int Alt;
        Alt = EAG.NodeBuf[Node];
        Ind;
        GenHeap(NodeName[Node], 0);
        WrSIS(" = ", SLEAGGen.NodeIdent[Alt], ";\n");
        for (n = 1; n <= EAG.MAlt[Alt].Arity; ++n)
        {
            Node1 = EAG.NodeBuf[Node + n];
            if (Node1 < 0)
            {
                V = -Node1;
                if (!EAG.Var[V].Def)
                {
                    SOAG.Error(SOAG.abnormalyError, "eSOAGGen.GenSynTraverse: Affix nicht definiert.");
                }
                else
                {
                    Ind;
                    GenHeap(NodeName[Node], n);
                    WrS(" = ");
                    GenAffix(V);
                    WrS("; ");
                    --AffixAppls[V];
                    if (AffixAppls[V] > 0)
                    {
                        GenIncRefCnt(V);
                    }
                    else
                    {
                        WrS("// komplementäre Referenzzählerbehandlung\n");
                    }
                    if (Optimize)
                    {
                        GenPopAffix(V);
                    }
                }
            }
            else
            {
                Ind;
                if (UseConst && EAG.MAlt[EAG.NodeBuf[Node1]].Arity == 0)
                {
                    GenHeap(NodeName[Node], n);
                    WrSIS(" = ", SLEAGGen.Leaf[EAG.NodeBuf[Node1]], "; ");
                    WrSIS("INC(Heap[", SLEAGGen.Leaf[EAG.NodeBuf[Node1]], "], refConst);\n");
                }
                else
                {
                    WrSIS("GetHeap(", EAG.MAlt[EAG.NodeBuf[Node1]].Arity, ", ");
                    GenVar(NodeName[Node1]);
                    WrS(");\n");
                    GenSynTraverseRefCnt(Node1);
                    Ind;
                    GenHeap(NodeName[Node], n);
                    WrS(" = ");
                    GenVar(NodeName[Node1]);
                    WrS(";\n");
                }
            }
        }
    }

    S = SOAG.SymOcc[SymOccInd].SymInd;
    IsPred = VisitNo == -1;
    for (AP = SOAG.SymOcc[SymOccInd].AffOcc.Beg; AP <= SOAG.SymOcc[SymOccInd].AffOcc.End;
            ++AP)
    {
        AN = AP - SOAG.SymOcc[SymOccInd].AffOcc.Beg;
        P = SOAG.AffOcc[AP].ParamBufInd;
        if (!EAG.ParamBuf[P].isDef && (SOAGVisitSeq.GetVisitNo(AP) == VisitNo || IsPred))
        {
            Node = EAG.ParamBuf[P].Affixform;
            SN = SymOccInd - SOAG.Rule[SOAG.SymOcc[SymOccInd].RuleInd].SymOcc.Beg;
            if (Node < 0)
            {
                V = -Node;
                if (!EAG.Var[V].Def)
                {
                    SOAG.Error(SOAG.abnormalyError, "eSOAGGen.GenSynTraverse: Affix nicht definiert.");
                }
                else if (!IsPred)
                {
                    Ind;
                    GenAffPos(S, AN);
                    WrS(" = ");
                    GenAffix(V);
                    WrS("; ");
                    --AffixAppls[V];
                    if (UseRefCnt && AffixAppls[V] > 0)
                    {
                        GenIncRefCnt(V);
                    }
                    else
                    {
                        WrS("// komplementäre Referenzzählerbehandlung\n");
                    }
                    if (Optimize)
                    {
                        GenPopAffix(V);
                    }
                    WrS("\n");
                }
            }
            else
            {
                Ind;
                if (UseConst && SLEAGGen.AffixPlace[P] >= 0)
                {
                    GenAffPos(S, AN);
                    WrSI(" = ", SLEAGGen.AffixPlace[P]);
                    if (UseRefCnt)
                    {
                        WrSIS("; INC(Heap[", SLEAGGen.AffixPlace[P], "], refConst)");
                    }
                    WrS(";\n");
                }
                else if (UseRefCnt)
                {
                    WrSIS("GetHeap(", EAG.MAlt[EAG.NodeBuf[Node]].Arity, ", ");
                    GenVar(NodeName[Node]);
                    WrS(");\n");
                    GenSynTraverseRefCnt(Node);
                    Ind;
                    GenAffPos(S, AN);
                    WrS(" = ");
                    GenVar(NodeName[Node]);
                    WrS(";\n");
                }
                else
                {
                    GenOverflowGuard(SLEAGGen.AffixSpace[P]);
                    Ind;
                    GenAffPos(S, AN);
                    WrS(" = NextHeap;\n");
                    Offset = 0;
                    GenSynTraverse(Node, Offset);
                    Ind;
                    GenHeapInc(Offset);
                }
            }
        }
    }
}

/**
 * IN: Symbolvorkommen, Visit-Nummer
 * OUT: -
 * SEM: Generierung der Analyseaktionen eines Besuchs für die besuchsrelevanten Affixparameter eines Symbolvorkommens
 */
void GenAnalPred(int SymOccInd, int VisitNo)
{
    int S;
    int AP;
    int AN;
    int Node;
    int V;
    int SN;
    bool IsPred;
    bool PosNeeded;
    void GenEqualErrMsg(int Var)
    {
        WrS("\"'");
        EAG.WriteVar(Out, Var);
        WrS("' failed in '");
        EAG.WriteNamedHNont(Out, SOAG.SymOcc[SymOccInd].SymInd);
        WrS("'\"");
    }

    void GenAnalErrMsg()
    {
        WrS("\"");
        EAG.WriteNamedHNont(Out, SOAG.SymOcc[SymOccInd].SymInd);
        WrS("\"");
    }

    /**
     * IN:  Index auf EAG.Var[] des def. Affixes, Index auf NodeName[] und Nr. des Sohnes im Heap
     * OUT: -
     * SEM: Generiert einen Vergleich zwischen einer Variable eines def. Affixes und einem Baumeintrag
     */
    void GenEqualPred(int V, int Node, int n)
    {
        WrS("Eq(");
        GenHeap(NodeName[Node], n);
        WrS(", ");
        GenAffix(V);
        WrS(", ");
        GenEqualErrMsg(V);
        WrS(");\n");
    }

    /**
     * IN:  zwei Indexe auf EAG.Var[]
     * OUT: -
     * SEM: Generiert einen Vergleich zwischen zwei Variablen der Felder Var[] (gen. Compiler)
     */
    void GenUnequalPred(int V1, int V2)
    {
        WrS("UnEq(");
        GenAffix(V1);
        WrS(", ");
        GenAffix(V2);
        WrS(", ");
        if (EAG.Var[V1].Num < 0)
        {
            GenEqualErrMsg(V1);
        }
        else
        {
            GenEqualErrMsg(V2);
        }
        WrS(");\n");
    }

    /**
     * SEM: Generierung einer Positionszuweisung, wenn notwendig
     */
    void GenPos(ref bool PosNeeded)
    {
        if (PosNeeded)
        {
            Ind;
            WrSIS("Pos = SemTree[TreeAdr + ", SubTreeOffset[SymOccInd], "].Pos;\n");
            PosNeeded = false;
        }
    }

    /**
     * IN: Knoten des Affixbaumes
     * OUT: -
     * SEM: Traversierung eines Affixbaumes und Ausgabe der Analyseaktionen für den zu generierenden Compiler
     */
    void GenAnalTraverse(int Node)
    {
        int Node1;
        int n;
        int V;
        int Alt;
        Ind;
        WrS("if (");
        Alt = EAG.NodeBuf[Node];
        if (UseConst && EAG.MAlt[Alt].Arity == 0)
        {
            GenVar(NodeName[Node]);
            WrSI(" != ", SLEAGGen.Leaf[Alt]);
        }
        else
        {
            GenHeap(NodeName[Node], 0);
            if (UseRefCnt)
            {
                WrS(".MOD(refConst)");
            }
            WrSI(" != ", SLEAGGen.NodeIdent[Alt]);
        }
        WrS(") AnalyseError(");
        GenVar(NodeName[Node]);
        WrS(", ");
        GenAnalErrMsg;
        WrS("); \n");
        for (n = 1; n <= EAG.MAlt[Alt].Arity; ++n)
        {
            Node1 = EAG.NodeBuf[Node + n];
            if (Node1 < 0)
            {
                V = -Node1;
                if (EAG.Var[V].Def)
                {
                    Ind;
                    GenEqualPred(V, Node, n);
                    --AffixAppls[V];
                    if (UseRefCnt)
                    {
                        GenFreeAffix(V);
                    }
                    if (Optimize)
                    {
                        GenPopAffix(V);
                    }
                }
                else
                {
                    EAG.Var[V].Def = true;
                    if (AffixOffset[V] != notApplied)
                    {
                        Ind;
                        GenAffixAssign(V);
                        GenHeap(NodeName[Node], n);
                        GenClose;
                        if (EAG.Var[EAG.Var[V].Neg].Def)
                        {
                            WrS("\n");
                            Ind;
                            GenUnequalPred(EAG.Var[V].Neg, V);
                            --AffixAppls[EAG.Var[V].Neg];
                            --AffixAppls[V];
                            if (UseRefCnt && AffixAppls[V] > 0)
                            {
                                GenIncRefCnt(V);
                            }
                            if (UseRefCnt)
                            {
                                GenFreeAffix(EAG.Var[V].Neg);
                            }
                            if (Optimize)
                            {
                                GenPopAffix(EAG.Var[V].Neg);
                                GenPopAffix(V);
                            }
                        }
                        else if (UseRefCnt)
                        {
                            GenIncRefCnt(V);
                        }
                    }
                }
            }
            else
            {
                Ind;
                GenVar(NodeName[Node1]);
                WrS(" = ");
                GenHeap(NodeName[Node], n);
                WrS(";\n");
                GenAnalTraverse(Node1);
            }
        }
    }

    S = SOAG.SymOcc[SymOccInd].SymInd;
    IsPred = VisitNo == -1;
    PosNeeded = !IsPred;
    for (AP = SOAG.SymOcc[SymOccInd].AffOcc.Beg; AP <= SOAG.SymOcc[SymOccInd].AffOcc.End;
            ++AP)
    {
        AN = AP - SOAG.SymOcc[SymOccInd].AffOcc.Beg;
        if (EAG.ParamBuf[SOAG.AffOcc[AP].ParamBufInd].isDef
                && (SOAGVisitSeq.GetVisitNo(AP) == VisitNo || IsPred))
        {
            Node = EAG.ParamBuf[SOAG.AffOcc[AP].ParamBufInd].Affixform;
            SN = SymOccInd - SOAG.Rule[SOAG.SymOcc[SymOccInd].RuleInd].SymOcc.Beg;
            if (Node < 0)
            {
                V = -Node;
                if (EAG.Var[V].Def)
                {
                    GenPos(PosNeeded);
                    Ind;
                    WrS("Eq(");
                    GenAffPos(S, AN);
                    WrS(", ");
                    GenAffix(V);
                    WrS(", ");
                    GenEqualErrMsg(V);
                    WrS(");\n");
                    --AffixAppls[V];
                    if (UseRefCnt)
                    {
                        GenFreeAffix(V);
                    }
                    if (Optimize)
                    {
                        GenPopAffix(V);
                    }
                    if (UseRefCnt)
                    {
                        Ind;
                        WrS("FreeHeap(");
                        GenAffPos(S, AN);
                        WrS(");\n");
                    }
                }
                else
                {
                    EAG.Var[V].Def = true;
                    if (!IsPred)
                    {
                        if (AffixOffset[V] != notApplied)
                        {
                            Ind;
                            GenAffixAssign(V);
                            GenAffPos(S, AN);
                            GenClose;
                            if (UseRefCnt)
                            {
                                WrS("// komplementäre Referenzzählerbehandlung");
                            }
                            WrS("\n");
                        }
                    }
                    if (EAG.Var[EAG.Var[V].Neg].Def)
                    {
                        GenPos(PosNeeded);
                        Ind;
                        WrS("UnEq(");
                        GenAffix(EAG.Var[V].Neg);
                        WrS(", ");
                        GenAffix(V);
                        WrS(", ");
                        GenEqualErrMsg(V);
                        WrS(");\n");
                        --AffixAppls[EAG.Var[V].Neg];
                        --AffixAppls[V];
                        if (UseRefCnt)
                        {
                            GenFreeAffix(EAG.Var[V].Neg);
                            GenFreeAffix(V);
                        }
                        if (Optimize)
                        {
                            GenPopAffix(EAG.Var[V].Neg);
                            GenPopAffix(V);
                        }
                    }
                }
            }
            else
            {
                GenPos(PosNeeded);
                Ind;
                GenVar(NodeName[Node]);
                WrS(" = ");
                GenAffPos(S, AN);
                WrS(";\n");
                GenAnalTraverse(Node);
                if (UseRefCnt)
                {
                    Ind;
                    WrS("FreeHeap(");
                    GenAffPos(S, AN);
                    WrS(");\n");
                }
            }
        }
    }
}

/**
 * IN: Symbolvorkommen, Visit-Nummer
 * OUT: -
 * SEM: Generierung eines Aufrufes der Prozedur 'Visit' für den zu generierenden Compiler
 */
void GenVisitCall(int SO, int VisitNo)
{
    Ind;
    WrSIS("Visit(TreeAdr + ", SubTreeOffset[SO], ", ");
    WrIS(VisitNo, ");\n");
}

/**
 * SEM: generriert nur Kommentar
 */
void GenLeave(int SO, int VisitNo)
{
    Ind;
    WrSIS("// Leave; VisitNo: ", VisitNo, "\n");
}

/**
 * IN: Symbolvorkommen eines Prädikates
 * OUT: -
 * SEM: Generierung des Aufrufes einer Prädikatprozedur
 */
void GenPredCall(int SO)
{
    int S;
    int AP;
    int AN;
    int AP1;
    int Node;
    int V;
    if (UseRefCnt)
    {
        for (AP = SOAG.SymOcc[SO].AffOcc.Beg; AP <= SOAG.SymOcc[SO].AffOcc.End; ++AP)
        {
            if (!EAG.ParamBuf[SOAG.AffOcc[AP].ParamBufInd].isDef)
            {
                AN = AP - SOAG.SymOcc[SO].AffOcc.Beg;
                V = -EAG.ParamBuf[SOAG.AffOcc[AP].ParamBufInd].Affixform;
                if (V > 0)
                {
                    Ind;
                    GenIncRefCnt(V);
                }
            }
        }
    }
    S = SOAG.SymOcc[SO].SymInd;
    Ind;
    WrSIS("Check", S, "(\"");
    EAG.WriteNamedHNont(Out, S);
    WrS("\", ");
    for (AP = SOAG.SymOcc[SO].AffOcc.Beg; AP <= SOAG.SymOcc[SO].AffOcc.End; ++AP)
    {
        Node = EAG.ParamBuf[SOAG.AffOcc[AP].ParamBufInd].Affixform;
        AN = AP - SOAG.SymOcc[SO].AffOcc.Beg;
        V = -Node;
        if (EAG.ParamBuf[SOAG.AffOcc[AP].ParamBufInd].isDef)
        {
            if (V > 0 && SOAG.DefAffOcc[V] == AP)
            {
                if (Optimize && AffixOffset[V] == optimizedStorage)
                {
                    AP1 = GetCorrespondedAffPos(SOAG.DefAffOcc[V]);
                    if (SOAG.StorageName[AP1] > 0)
                    {
                        GenAffPos(S, AN);
                    }
                    else
                    {
                        WrSI("GV", -SOAG.StorageName[AP1]);
                    }
                }
                else if (AffixOffset[V] == notApplied)
                {
                    GenAffPos(S, AN);
                }
                else
                {
                    GenAffix(V);
                }
            }
            else
            {
                GenAffPos(S, AN);
            }
        }
        else
        {
            if (Node > 0)
            {
                GenAffPos(S, AN);
            }
            else
            {
                GenAffix(V);
            }
        }
        if (AP != SOAG.SymOcc[SO].AffOcc.End)
        {
            WrS(", ");
        }
        else
        {
            WrS(");\n");
        }
    }
    for (AP = SOAG.SymOcc[SO].AffOcc.Beg; AP <= SOAG.SymOcc[SO].AffOcc.End; ++AP)
    {
        AN = AP - SOAG.SymOcc[SO].AffOcc.Beg;
        V = -EAG.ParamBuf[SOAG.AffOcc[AP].ParamBufInd].Affixform;
        if (V > 0)
        {
            if (EAG.ParamBuf[SOAG.AffOcc[AP].ParamBufInd].isDef)
            {
                if (AffixOffset[V] == optimizedStorage)
                {
                    AP1 = GetCorrespondedAffPos(SOAG.DefAffOcc[V]);
                    if (SOAG.StorageName[AP1] > 0)
                    {
                        Ind;
                        WrSIS("Stacks.Push(Stack", SOAG.StorageName[AP1], ", ");
                        GenAffPos(S, AN);
                        WrS(");\n");
                    }
                }
                else if (AffixOffset[V] == notApplied)
                {
                    Ind;
                    WrS("FreeHeap(");
                    GenAffPos(S, AN);
                    WrS("); // Dummy-Variable\n");
                }
            }
            else
            {
                --AffixAppls[V];
                if (UseRefCnt)
                {
                    GenFreeAffix(V);
                }
                if (Optimize)
                {
                    GenPopAffix(V);
                }
            }
        }
    }
}

/**
 * IN:  Regel
 * OUT: -
 * SEM: Generierung der Variablendeklarationen einer Regel
 */
void GenVarDecls(int R)
{
    int SO;
    int i;
    WrS("IndexType TreeAdr;\n");
    WrS("IndexType VI;\n");
    WrS("SemTreeEntry S;\n");
    if (LocalVars[R] > 0)
    {
        for (i = 1; i <= LocalVars[R]; ++i)
        {
            WrS("HeapType ");
            GenVar(i);
            WrS(";\n");
        }
    }
}

/**
 * IN:  Regel, Nummer des Visit-Sequenz-Eintrages, Notwendigkeit der Positionszuweisung
 * OUT: -
 * SEM: Generierung der Positionszuweisung vor Prädikatprozeduraufrufen;
 *      zugewiesen wird die Position des vorhergehenden Visits
 */
void GenPredPos(int R, int i, ref bool PosNeeded)
{
    int k;
    if (PosNeeded)
    {
        --i;
        while (cast(SOAG.Visit) SOAG.VS[i] is null && cast(SOAG.Leave) SOAG.VS[i] is null && i > SOAG.Rule[R].VS.Beg)
        {
            --i;
        }
        if (cast(SOAG.Visit) SOAG.VS[i] !is null)
        {
            k = SubTreeOffset[(cast(SOAG.Visit) SOAG.VS[i]).SymOcc];
        }
        else
        {
            k = SOAG.Rule[R].SymOcc.Beg;
        }
        Ind;
        WrSIS("Pos = SemTree[TreeAdr + ", k, "].Pos;\n");
        PosNeeded = false;
    }
}

/**
 * IN: Regelnummer
 * OUT: -
 * SEM: Generiert Code für die Visit-Sequenzen einer Regel
 */
void GenVisitRule(int R)
{
    int SO;
    int VN;
    int VisitNo;
    int i;
    int S;
    int NontCnt;
    bool onlyoneVisit;
    bool first;
    bool PosNeeded;

    Indent = 0;
    WrSIS("void VisitRule", R, "(long Symbol, int VisitNo)\n");
    WrS("/*\n");
    Protocol.Out = Out;
    WrS(" * ");
    Protocol.WriteRule(R);
    WrS(" */\n");
    Protocol.Out = IO.Msg;
    WrS("{\n");
    GenVarDecls(R);
    INC(Indent, cTab);
    NontCnt = 1;
    for (SO = SOAG.Rule[R].SymOcc.Beg + 1; SO <= SOAG.Rule[R].SymOcc.End; ++SO)
    {
        if (!SOAG.IsPredNont(SO))
        {
            ++NontCnt;
        }
    }
    SO = SOAG.Rule[R].SymOcc.Beg;
    Ind;
    WrS("if (VisitNo == syntacticPart)\n");
    Ind;
    WrS("{\n");
    INC(Indent, cTab);
    Ind;
    WrSIS("if (NextSemTree >= SemTree.length - ", NontCnt, ") ExpandSemTree;\n");
    Ind;
    WrS("TreeAdr = SemTree[Symbol].Adr;\n");
    Ind;
    WrS("SemTree[Symbol].Adr = NextSemTree;\n");
    Ind;
    WrS("SemTree[Symbol].Pos = PosTree[TreeAdr];\n");
    Ind;
    WrSIS("INC(AffixVarCount, ", GetAffixCount(R), ");\n");
    if (AffixVarCount[R] > 0)
    {
        Ind;
        WrSIS("if (NextVar >= Var.length - ", AffixVarCount[R], ") ExpandVar;\n");
        Ind;
        WrSIS("SemTree[Symbol].VarInd = NextVar; INC(NextVar, ", AffixVarCount[R], ");\n");
    }
    else
    {
        Ind;
        WrS("SemTree[Symbol].VarInd = nil;\n");
    }
    Ind;
    WrS("SemTree[NextSemTree] = SemTree[Symbol];\n");
    Ind;
    WrS("INC(NextSemTree);\n");
    for (SO = SOAG.Rule[R].SymOcc.Beg + 1; SO <= SOAG.Rule[R].SymOcc.End; ++SO)
    {
        if (!SOAG.IsPredNont(SO))
        {
            Ind;
            WrS("NEW(S);\n");
            Ind;
            WrSIS("S.Adr = Tree[TreeAdr + ", SubTreeOffset[SO], "];\n");
            Ind;
            WrSIS("S.Rule = ", FirstRule[SOAG.SymOcc[SO].SymInd] - 1, " + MOD(Tree[S.Adr], hyperArityConst);\n");
            Ind;
            WrS("SemTree[NextSemTree] = S; INC(NextSemTree);\n");
        }
    }
    first = true;
    for (SO = SOAG.Rule[R].SymOcc.Beg + 1; SO <= SOAG.Rule[R].SymOcc.End; ++SO)
    {
        if (!SOAG.IsPredNont(SO))
        {
            if (first)
            {
                Ind;
                WrS("TreeAdr = SemTree[Symbol].Adr;\n");
                first = false;
            }
            Ind;
            WrSIS("Visit(TreeAdr + ", SubTreeOffset[SO], ", syntacticPart);\n");
        }
    }
    DEC(Indent, cTab);
    Ind;
    WrS("}\n");
    Ind;
    WrS("else\n");
    Ind;
    WrS("{\n");
    INC(Indent, cTab);
    Ind;
    WrS("TreeAdr = SemTree[Symbol].Adr;\n");
    if (AffixVarCount[R] > 0)
    {
        Ind;
        WrS("VI = SemTree[Symbol].VarInd;\n\n");
    }
    if (SOAGVisitSeq.GetMaxVisitNo(SOAG.Rule[R].SymOcc.Beg) == 1)
    {
        onlyoneVisit = true;
    }
    else
    {
        onlyoneVisit = false;
        Ind;
        WrS("switch (VisitNo)\n");
        Ind;
        WrS("{\n");
        INC(Indent, cTab);
        Ind;
        WrS("case 1:\n");
        INC(Indent, cTab);
    }
    VisitNo = 1;
    PosNeeded = true;
    Ind;
    WrS("// Visit-beginnende Analyse\n");
    GenAnalPred(SOAG.Rule[R].SymOcc.Beg, VisitNo);
    for (i = SOAG.Rule[R].VS.Beg; i <= SOAG.Rule[R].VS.End; ++i)
    {
        if (cast(SOAG.Visit) SOAG.VS[i] !is null)
        {
            SO = (cast(SOAG.Visit) SOAG.VS[i]).SymOcc;
            S = SOAG.SymOcc[SO].SymInd;
            VN = (cast(SOAG.Visit) SOAG.VS[i]).VisitNo;
            Ind;
            WrS("// Synthese\n");
            GenSynPred(SO, VN);
            GenVisitCall(SO, VN);
            Ind;
            WrS("// Analyse\n");
            GenAnalPred(SO, VN);
            WrS("\n");
            PosNeeded = true;
        }
        else if (cast(SOAG.Call) SOAG.VS[i] !is null)
        {
            SO = (cast(SOAG.Call) SOAG.VS[i]).SymOcc;
            Ind;
            WrS("// Synthese\n");
            GenSynPred(SO, -1);
            GenPredPos(R, i, PosNeeded);
            GenPredCall(SO);
            Ind;
            WrS("// Analyse\n");
            GenAnalPred(SO, -1);
            WrS("\n");
        }
        else if (cast(SOAG.Leave) SOAG.VS[i] !is null)
        {
            SO = SOAG.Rule[R].SymOcc.Beg;
            VN = (cast(SOAG.Leave) SOAG.VS[i]).VisitNo;
            ASSERT(VN == VisitNo);
            Ind;
            WrS("// Visit-abschließende Synthese\n");
            GenSynPred(SO, VisitNo);
            GenLeave(SO, VisitNo);
            if (VisitNo < SOAGVisitSeq.GetMaxVisitNo(SO))
            {
                Ind;
                WrS("break;\n");
                DEC(Indent, cTab);
                ++VisitNo;
                PosNeeded = true;
                Ind;
                WrSIS("case ", VisitNo, ":\n");
                INC(Indent, cTab);
                Ind;
                WrS("// Visit-beginnende Analyse\n");
                GenAnalPred(SO, VisitNo);
            }
            else
            {
                if (!onlyoneVisit)
                {
                    Ind;
                    WrS("break;\n");
                }
                DEC(Indent, cTab);
            }
        }
    }
    if (!onlyoneVisit)
    {
        Ind;
        WrS("default: assert(0);\n");
        DEC(Indent, cTab);
        Ind;
        WrS("}\n");
        DEC(Indent, cTab);
    }
    Ind;
    WrS("}\n");
    WrS("}\n\n");
}

/**
 * SEM: Generierung der Prozedur 'Visit', die die Besuche auf die entsprechenden Regeln verteilt
 */
void GenVisit()
{
    int R;
    Indent = 0;
    WrS("void Visit(long Symbol, int VisitNo)\n");
    WrS("{\n");
    INC(Indent, cTab);
    Ind;
    WrS("switch (SemTree[Symbol].Rule)\n");
    Ind;
    WrS("{\n");
    INC(Indent, cTab);
    for (R = SOAG.firstRule; R <= SOAG.NextRule - 1; ++R)
    {
        if (SOAG.IsEvaluatorRule(R))
        {
            Ind;
            WrSIS("case ", R, ": ");
            WrSIS("VisitRule", R, "(Symbol, VisitNo); break;\n");
        }
    }
    Ind;
    WrS("default: assert(0);\n");
    DEC(Indent, cTab);
    Ind;
    WrS("}\n");
    WrS("}\n\n");
}

/**
 * SEM: Generierung der Konstanten für den Zugriff auf AffPos[] im generierten Compiler
 */
void GenConstDeclarations()
{
    int S;
    for (S = SOAG.firstSym; S <= SOAG.NextSym - 1; ++S)
    {
        WrSIS("const S", S, " = ");
        WrIS(SOAG.Sym[S].AffPos.Beg, "; // ");
        EAG.WriteHNont(Out, S);
        WrS("\n");
    }
}

/**
 * SEM: Generierung der Deklarationen der globalen Variablen und Stacks
 */
void GenStackDeclarations()
{
    int V;
    if (SOAGOptimizer.GlobalVar > 0 || SOAGOptimizer.StackVar > 0)
    {
        for (V = SOAGOptimizer.firstGlobalVar; V <= SOAGOptimizer.GlobalVar; ++V)
        {
            WrSIS("HeapType GV", V, ";\n");
        }
        for (V = SOAGOptimizer.firstStackVar; V <= SOAGOptimizer.StackVar; ++V)
        {
            WrSIS("Stacks.Stack Stack", V, ";\n");
        }
        WrS("\n");
    }
}

/**
 * SEM: Generierung der Initialisierungen der Stacks
 */
void GenStackInit()
{
    int S;
    if (SOAGOptimizer.StackVar > 0)
    {
        for (S = SOAGOptimizer.firstStackVar; S <= SOAGOptimizer.StackVar; ++S)
        {
            WrSIS("Stacks.New(Stack", S, ", 8);\n");
        }
    }
}

/**
 * SEM: Generierung des Compiler-Moduls
 */
void GenerateModule()
{
    int R;
    char[] Name = new char[EAG.BaseNameLen + 10];
    IO.TextIn Fix;
    int StartRule;

    void InclFix(char Term)
    {
        char c;
        IO.Read(Fix, c);
        while (c != Term)
        {
            if (c == '\x00')
            {
                throw new Exception("error: unexpected end of eSOAG.Fix");
            }
            IO.Write(Out, c);
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

    IO.OpenIn(Fix, "fix/eSOAG.fix.d", Error);
    if (Error)
    {
        throw new Exception("error: could not open eSOAG.Fix");
    }
    Append(Name, EAG.BaseName, "Eval");
    IO.CreateModOut(Out, Name);
    SLEAGGen.InitGen(Out, SLEAGGen.sSweepPass);
    InclFix('$');
    WrS(Name);
    InclFix('$');
    WrI(HyperArity());
    InclFix('$');
    GenConstDeclarations;
    InclFix('$');
    if (Optimize)
    {
        GenStackDeclarations;
    }
    SLEAGGen.GenDeclarations;
    InclFix('$');
    SLEAGGen.GenPredProcs;
    for (R = SOAG.firstRule; R <= SOAG.NextRule - 1; ++R)
    {
        if (SOAG.IsEvaluatorRule(R))
        {
            ComputeNodeNames(R);
            ComputeAffixOffset(R);
            GenVisitRule(R);
        }
    }
    GenVisit;
    EmitGen.GenEmitProc(Out);
    InclFix('$');
    WrI(SOAG.NextPartNum);
    InclFix('$');
    if (Optimize)
    {
        GenStackInit;
    }
    StartRule = FirstRule[SOAG.SymOcc[SOAG.Sym[EAG.StartSym].FirstOcc].RuleInd];
    InclFix('$');
    if (StartRule - 1 != 0)
    {
        WrIS(StartRule - 1, " + ");
    }
    InclFix('$');
    WrSI("S", EAG.StartSym);
    InclFix('$');
    EmitGen.GenEmitCall(Out);
    InclFix('$');
    EmitGen.GenShowHeap(Out);
    InclFix('$');
    if (Optimize)
    {
        WrI(SOAGOptimizer.StackVar);
    }
    else
    {
        WrI(0);
    }
    InclFix('$');
    if (Optimize)
    {
        WrI(SOAGOptimizer.GlobalVar);
    }
    else
    {
        WrI(0);
    }
    InclFix('$');
    WrS(EAG.BaseName);
    WrS("Eval");
    InclFix('$');
    IO.Update(Out);
    if (ShowMod)
    {
        IO.Show(Out);
    }
    else
    {
        IO.Compile(Out, Error);
        if (Error)
        {
            IO.Show(Out);
        }
    }
    SLEAGGen.FinitGen;
    IO.CloseIn(Fix);
    IO.CloseOut(Out);
}

/**
 * SEM: Steuerung der Generierung
 */
void Generate()
{
    UseConst = !IO.IsOption('c');
    UseRefCnt = !IO.IsOption('r');
    ShowMod = IO.IsOption('m');
    Optimize = !IO.IsOption('o');
    SOAGPartition.Compute;
    SOAGVisitSeq.Generate;
    if (Optimize)
    {
        SOAGOptimizer.Optimize;
    }
    IO.WriteText(IO.Msg, "SOAG writing ");
    IO.WriteString(IO.Msg, EAG.BaseName);
    IO.WriteText(IO.Msg, "   ");
    if (Optimize)
    {
        IO.WriteText(IO.Msg, "+o ");
    }
    else
    {
        IO.WriteText(IO.Msg, "-o ");
    }
    IO.Update(IO.Msg);
    if (EAG.Performed(SET(EAG.analysed, EAG.predicates)))
    {
        Init;
        GenerateModule;
        if (!Error)
        {
            INCL(EAG.History, EAG.isSSweep);
            INCL(EAG.History, EAG.hasEvaluator);
        }
    }
}

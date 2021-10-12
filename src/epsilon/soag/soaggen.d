module epsilon.soag.soaggen;

import EAG = epsilon.eag;
import EmitGen = epsilon.emitgen;
import SLAGGen = epsilon.slaggen;
import epsilon.settings;
import io : Input, read;
import log;
import runtime;
import optimizer = epsilon.soag.optimizer;
import partition = epsilon.soag.partition;
import Protocol = epsilon.soag.protocol;
import SOAG = epsilon.soag.soag;
import VisitSeq = epsilon.soag.visitseq;
import std.bitmanip : BitArray;
import std.stdio;

private const firstAffixOffset = 0;
private const optimizedStorage = -1;
private const notApplied = -2;
private bool UseConst;
private bool UseRefCnt;
private bool Optimize;
private int[] LocalVars;
private int[] NodeName;
private int[] AffixOffset;
private int[] AffixVarCount;
private int[] SubTreeOffset;
private int[] FirstRule;
private int[] AffixAppls;
private File output;
private bool Close;

/**
 * SEM: Steuerung der Generierung
 */
public string Generate(Settings settings)
in (EAG.Performed(EAG.analysed | EAG.predicates))
{
    UseConst = !settings.c;
    UseRefCnt = !settings.r;
    Optimize = !settings.o;
    partition.Compute;
    VisitSeq.Generate;
    if (Optimize)
        optimizer.Optimize;
    info!"SOAG writing %s"(EAG.BaseName);
    if (Optimize)
        info!"optimize";
    else
        info!"don't optimize";
    Init;

    const fileName = GenerateModule(settings);

    EAG.History |= EAG.isSweep;
    EAG.History |= EAG.hasEvaluator;
    return fileName;
}

/**
 * IN:  Regel
 * OUT: -
 * SEM: Berechnet im Feld NodeNames für alle Affixbaumanalysen der Regel
 *      die Namen der temp. Variablen für die Baumknoten;
 *      die maximale Variablenummer der Regel wird in LocalVars[] abgelegt
 */
private void ComputeNodeNames(int R) @nogc nothrow
{
    int Var;
    int ProcVar;
    int AP;
    int Node;
    int SO;
    int PBI;

    /**
     * IN: Knoten in NodeBuf[], Variablenname
     * OUT: -
     * SEM: Berechnet für jeden Knoten des Teilbaums NodeBuf[Node]
     *      die temp. Variable für die Baumanalyse oder -synthese
     */
    void Traverse(int Node, ref int Var)
    {
        int Node1;
        const Arity = EAG.MAlt[EAG.NodeBuf[Node]].Arity;

        ++Var;
        NodeName[Node] = Var;
        for (size_t n = 1; n <= Arity; ++n)
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
private int GetCorrespondedAffPos(int AP) @nogc nothrow @safe
{
    const SO = SOAG.AffOcc[AP].SymOccInd;
    const AN = AP - SOAG.SymOcc[SO].AffOcc.Beg;

    return SOAG.Sym[SOAG.SymOcc[SO].SymInd].AffPos.Beg + AN;
}

/**
 * IN:  Regel
 * OUT: -
 * SEM: berechnet im Feld AffixOffset[], das parallel zu EAG.Var liegt,
 *      den Offset der Affixvariablen im Feld Var[] des generierten Compilers;
 *      alle nicht-applizierten Affixvariablen (AffixAppls[]=0) werden ausgelassen
 * PRE: AffixAppls[] muss berechnet sein
 */
private void ComputeAffixOffset(int R) @nogc nothrow @safe
{
    EAG.ScopeDesc Scope;

    if (auto ordRule = cast(SOAG.OrdRule) SOAG.Rule[R])
    {
        Scope = ordRule.Alt.Scope;
    }
    else if (auto emptyRule = cast(SOAG.EmptyRule) SOAG.Rule[R])
    {
        EAG.Rule EAGRule = emptyRule.Rule;

        if (auto opt = cast(EAG.Opt) EAGRule)
            Scope = opt.Scope;
        else if (auto rep = cast(EAG.Rep) EAGRule)
            Scope = rep.Scope;
    }

    int Offset = firstAffixOffset;

    foreach (A; Scope.Beg .. Scope.End)
    {
        if (AffixAppls[A] > 0)
        {
            if (Optimize)
            {
                const AP = GetCorrespondedAffPos(SOAG.DefAffOcc[A]);

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
private int GetAffixCount(int R) @nogc nothrow @safe
{
    EAG.ScopeDesc Scope;

    if (auto ordRule = cast(SOAG.OrdRule) SOAG.Rule[R])
    {
        Scope = ordRule.Alt.Scope;
    }
    else if (auto emptyRule = cast(SOAG.EmptyRule) SOAG.Rule[R])
    {
        EAG.Rule EAGRule = emptyRule.Rule;

        if (auto opt = cast(EAG.Opt) EAGRule)
            Scope = opt.Scope;
        else if (auto rep = cast(EAG.Rep) EAGRule)
            Scope = rep.Scope;
    }
    return Scope.End - Scope.Beg;
}

/**
 * IN:  -
 * OUT: Hyper-Arity-Konstante
 * SEM: Liefert die Arity-Konstante für den Ableitungsbaum, der durch den Parser erzeugt wird;
 *      müsste eigentlich von SLAG geliefert werden (in Sweep wurde es auch intern definiert,
 *      deshalb wird es hier für spätere Module exportiert)
 */
private int HyperArity() nothrow
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
        if (cast(EAG.Opt) EAG.HNont[N].Def || cast(EAG.Rep) EAG.HNont[N].Def)
            ++i;
        if (i > Max)
            Max = i;
    }
    i = 1;
    while (i <= Max)
        i = i * 2;
    return i;
}

/**
 * SEM: Initialisierung der Datenstrukturen des Moduls
 */
private void Init() nothrow
{
    int R;
    int SO;
    int S;
    int Offset;

    LocalVars = new int[SOAG.NextRule];
    AffixVarCount = new int[SOAG.NextRule];
    AffixOffset = new int[EAG.NextVar];
    NodeName = new int[EAG.NextNode];
    SubTreeOffset = new int[SOAG.NextSymOcc];
    FirstRule = new int[SOAG.NextSym];
    AffixAppls = new int[EAG.NextVar];
    for (size_t i = SOAG.firstRule; i < SOAG.NextRule; ++i)
    {
        LocalVars[i] = 0;
        AffixVarCount[i] = -1;
    }
    for (size_t i = EAG.firstNode; i < EAG.NextNode; ++i)
    {
        NodeName[i] = -1;
    }
    for (size_t i = EAG.firstVar; i < EAG.NextVar; ++i)
    {
        EAG.Var[i].Def = false;
        AffixAppls[i] = SOAG.AffixApplCnt[i];
    }
    for (R = SOAG.firstRule; R < SOAG.NextRule; ++R)
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
    for (S = SOAG.firstSym; S < SOAG.NextSym; ++S)
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

private void GenHeap(int Var, int Offset) @safe
{
    output.write("Heap[");
    if (Var > 0)
        GenVar(Var);
    else
        output.write("NextHeap");
    if (Offset > 0)
        output.write(" + ", Offset);
    else if (Offset < 0)
        output.write(" - ", -Offset);
    output.write("]");
}

private void GenOverflowGuard(int n) @safe
{
    if (n > 0)
        output.writeln("if (NextHeap >= Heap.length - ", n, ") EvalExpand;");
}

/**
 * IN:  Symbol, Nummer eines Affixparameter relativ zum Symbolvorkommen
 * OUT: -
 * SEM: Generierung eines Zugriffs auf die Instanz einer Affixposition
 */
private void GenAffPos(int S, int AN) @safe
{
    output.write("AffPos[S", S, " + ", AN, "]");
}

/**
 * IN: Affixnummer
 * OUT: -
 * SEM: Generiert einen Zugriff auf den Inhalt eines Affixes
 */
private void GenAffix(int V) @safe
in (AffixOffset[V] != notApplied)
{
    int AP;

    if (AffixOffset[V] == optimizedStorage)
    {
        AP = GetCorrespondedAffPos(SOAG.DefAffOcc[V]);
        if (SOAG.StorageName[AP] > 0)
            output.write("Stacks.Top(Stack", SOAG.StorageName[AP], ") ");
        else
            output.write("GV", -SOAG.StorageName[AP]);
    }
    else
    {
        output.write("Var[VI + ", AffixOffset[V], "]");
    }
}

/**
 * IN: Affix
 * OUT: -
 * SEM: Generierung einer Zuweisung zu einer Instanz einer Affixvariable;
 *      nur in Kombination mit der Prozedur GenClose zu verwenden
 */
private void GenAffixAssign(int V) @safe
in (AffixOffset[V] != notApplied)
{
    int AP;

    if (AffixOffset[V] == optimizedStorage)
    {
        AP = GetCorrespondedAffPos(SOAG.DefAffOcc[V]);
        if (SOAG.StorageName[AP] > 0)
        {
            output.write("Stacks.Push(Stack", SOAG.StorageName[AP], ", ");
            Close = true;
        }
        else
        {
            output.write("GV", -SOAG.StorageName[AP], " = ");
            Close = false;
        }
    }
    else
    {
        output.write("Var[VI + ", AffixOffset[V], "] = ");
        Close = false;
    }
}

private void GenClose() @safe
{
    if (Close)
        output.write(");");
    else
        output.write(";");
}

/**
 * IN: Affixvariable oder (< 0) lokale Variable
 * OUT: -
 * SEM: Generiert eine Erhöhung des Referenzzählers des Knotens auf den das Affixes
 *      bzw. der Index verweist, im Falle eines Stacks wird globale Var. RefIncVar verwendet
 */
private void GenIncRefCnt(int Var) @safe
{
    output.write("Heap[");
    if (Var < 0)
        GenVar(-Var);
    else
        GenAffix(Var);
    output.writeln("] += refConst;");
}

/**
 * IN: Affixvariable
 * OUT: -
 * SEM: generiert die Freigabe des alloziierten Speichers,
 *      wenn die Affixvariable das letzte mal appliziert wurde (AffixAppls = 0)
 */
private void GenFreeAffix(int V) @safe
{
    if (AffixAppls[V] == 0)
    {
        output.write("FreeHeap(");
        GenAffix(V);
        output.writeln(");");
    }
}

/**
 * IN: Affixvariable
 * OUT: -
 * SEM: generiert die Kellerspeicherfreigabe,
 *      wenn die Affixvariable das letzte mal appliziert wurde (AffixAppls = 0)
 */
private void GenPopAffix(int V) @safe
{
    if (AffixAppls[V] == 0)
    {
        if (AffixOffset[V] == optimizedStorage)
        {
            const AP = GetCorrespondedAffPos(SOAG.DefAffOcc[V]);

            if (SOAG.StorageName[AP] > 0)
                output.writeln("Stacks.Pop(Stack", SOAG.StorageName[AP], ");");
            else
                output.writeln("GV", -SOAG.StorageName[AP], " = -1;");
        }
    }
}

/**
 * IN: Symbolvorkommen
 * OUT: -
 * SEM: Generierung der Syntheseaktionen eines Besuchs für die besuchsrelevanten Affixparameter eines Symbolvorkommens
 */
private void GenSynPred(int SymOccInd, int VisitNo)
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
        const Alt = EAG.NodeBuf[Node];

        GenHeap(-1, Offset);
        output.writeln(" = ", SLAGGen.NodeIdent[Alt], ";");
        Offset1 = Offset;
        Offset += 1 + EAG.MAlt[Alt].Arity;
        for (n = 1; n <= EAG.MAlt[Alt].Arity; ++n)
        {
            Node1 = EAG.NodeBuf[Node + n];
            if (Node1 < 0)
            {
                V = -Node1;
                if (!EAG.Var[V].Def)
                {
                    SOAG.Error(SOAG.abnormalError, "eSOAGGen.GenSynTraverse: Affix nicht definiert.");
                }
                else
                {
                    GenHeap(-1, Offset1 + n);
                    output.write(" = ");
                    GenAffix(V);
                    output.writeln(";");
                    --AffixAppls[V];
                    if (UseRefCnt)
                        GenFreeAffix(V);
                    if (Optimize)
                        GenPopAffix(V);
                }
            }
            else
            {
                GenHeap(-1, Offset1 + n);
                output.write(" = ");
                if (UseConst && EAG.MAlt[EAG.NodeBuf[Node1]].Arity == 0)
                {
                    output.writeln(SLAGGen.Leaf[EAG.NodeBuf[Node1]], ";");
                }
                else
                {
                    output.writeln("NextHeap + ", Offset, ";");
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
        const Alt = EAG.NodeBuf[Node];

        GenHeap(NodeName[Node], 0);
        output.writeln(" = ", SLAGGen.NodeIdent[Alt], ";");
        for (n = 1; n <= EAG.MAlt[Alt].Arity; ++n)
        {
            Node1 = EAG.NodeBuf[Node + n];
            if (Node1 < 0)
            {
                V = -Node1;
                if (!EAG.Var[V].Def)
                {
                    SOAG.Error(SOAG.abnormalError, "eSOAGGen.GenSynTraverse: Affix nicht definiert.");
                }
                else
                {
                    GenHeap(NodeName[Node], n);
                    output.write(" = ");
                    GenAffix(V);
                    output.write("; ");
                    --AffixAppls[V];
                    if (AffixAppls[V] > 0)
                        GenIncRefCnt(V);
                    else
                        output.writeln("// komplementäre Referenzzählerbehandlung");
                    if (Optimize)
                        GenPopAffix(V);
                }
            }
            else
            {
                if (UseConst && EAG.MAlt[EAG.NodeBuf[Node1]].Arity == 0)
                {
                    GenHeap(NodeName[Node], n);
                    output.write(" = ", SLAGGen.Leaf[EAG.NodeBuf[Node1]], "; ");
                    output.writeln("Heap[", SLAGGen.Leaf[EAG.NodeBuf[Node1]], "] += refConst;");
                }
                else
                {
                    output.write("GetHeap(", EAG.MAlt[EAG.NodeBuf[Node1]].Arity, ", ");
                    GenVar(NodeName[Node1]);
                    output.writeln(");");
                    GenSynTraverseRefCnt(Node1);
                    GenHeap(NodeName[Node], n);
                    output.write(" = ");
                    GenVar(NodeName[Node1]);
                    output.writeln(";");
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
        if (!EAG.ParamBuf[P].isDef && (VisitSeq.GetVisitNo(AP) == VisitNo || IsPred))
        {
            Node = EAG.ParamBuf[P].Affixform;
            SN = SymOccInd - SOAG.Rule[SOAG.SymOcc[SymOccInd].RuleInd].SymOcc.Beg;
            if (Node < 0)
            {
                V = -Node;
                if (!EAG.Var[V].Def)
                {
                    SOAG.Error(SOAG.abnormalError, "eSOAGGen.GenSynTraverse: Affix nicht definiert.");
                }
                else if (!IsPred)
                {
                    GenAffPos(S, AN);
                    output.write(" = ");
                    GenAffix(V);
                    output.write("; ");
                    --AffixAppls[V];
                    if (UseRefCnt && AffixAppls[V] > 0)
                        GenIncRefCnt(V);
                    else
                        output.writeln("// komplementäre Referenzzählerbehandlung");
                    if (Optimize)
                        GenPopAffix(V);
                    output.writeln;
                }
            }
            else
            {
                if (UseConst && SLAGGen.AffixPlace[P] >= 0)
                {
                    GenAffPos(S, AN);
                    output.write(" = ", SLAGGen.AffixPlace[P]);
                    if (UseRefCnt)
                        output.write("; Heap[", SLAGGen.AffixPlace[P], "] += refConst");
                    output.writeln(";");
                }
                else if (UseRefCnt)
                {
                    output.write("GetHeap(", EAG.MAlt[EAG.NodeBuf[Node]].Arity, ", ");
                    GenVar(NodeName[Node]);
                    output.writeln(");");
                    GenSynTraverseRefCnt(Node);
                    GenAffPos(S, AN);
                    output.write(" = ");
                    GenVar(NodeName[Node]);
                    output.writeln(";");
                }
                else
                {
                    GenOverflowGuard(SLAGGen.AffixSpace[P]);
                    GenAffPos(S, AN);
                    output.writeln(" = NextHeap;");
                    Offset = 0;
                    GenSynTraverse(Node, Offset);
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
private void GenAnalPred(int SymOccInd, int VisitNo) @safe
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
        output.write(`"'`);
        output.write(EAG.VarRepr(Var));
        output.write("' failed in '");
        output.write(EAG.NamedHNontRepr(SOAG.SymOcc[SymOccInd].SymInd));
        output.write(`'"`);
    }

    void GenAnalErrMsg()
    {
        output.write(`"`);
        output.write(EAG.NamedHNontRepr(SOAG.SymOcc[SymOccInd].SymInd));
        output.write(`"`);
    }

    /**
     * IN:  Index auf EAG.Var[] des def. Affixes, Index auf NodeName[] und Nr. des Sohnes im Heap
     * OUT: -
     * SEM: Generiert einen Vergleich zwischen einer Variable eines def. Affixes und einem Baumeintrag
     */
    void GenEqualPred(int V, int Node, int n)
    {
        output.write("Eq(");
        GenHeap(NodeName[Node], n);
        output.write(", ");
        GenAffix(V);
        output.write(", ");
        GenEqualErrMsg(V);
        output.writeln(");");
    }

    /**
     * IN:  zwei Indexe auf EAG.Var[]
     * OUT: -
     * SEM: Generiert einen Vergleich zwischen zwei Variablen der Felder Var[] (gen. Compiler)
     */
    void GenUnequalPred(int V1, int V2)
    {
        output.write("UnEq(");
        GenAffix(V1);
        output.write(", ");
        GenAffix(V2);
        output.write(", ");
        if (EAG.Var[V1].Num < 0)
            GenEqualErrMsg(V1);
        else
            GenEqualErrMsg(V2);
        output.writeln(");");
    }

    /**
     * SEM: Generierung einer Positionszuweisung, wenn notwendig
     */
    void GenPos(ref bool PosNeeded)
    {
        if (PosNeeded)
        {
            output.writeln("Pos = SemTree[TreeAdr + ", SubTreeOffset[SymOccInd], "].Pos;");
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
        const Alt = EAG.NodeBuf[Node];

        output.write("if (");
        if (UseConst && EAG.MAlt[Alt].Arity == 0)
        {
            GenVar(NodeName[Node]);
            output.write(" != ", SLAGGen.Leaf[Alt]);
        }
        else
        {
            GenHeap(NodeName[Node], 0);
            if (UseRefCnt)
                output.write(".MOD(refConst)");
            output.write(" != ", SLAGGen.NodeIdent[Alt]);
        }
        output.write(") AnalyseError(");
        GenVar(NodeName[Node]);
        output.write(", ");
        GenAnalErrMsg;
        output.writeln(");");
        for (n = 1; n <= EAG.MAlt[Alt].Arity; ++n)
        {
            Node1 = EAG.NodeBuf[Node + n];
            if (Node1 < 0)
            {
                V = -Node1;
                if (EAG.Var[V].Def)
                {
                    GenEqualPred(V, Node, n);
                    --AffixAppls[V];
                    if (UseRefCnt)
                        GenFreeAffix(V);
                    if (Optimize)
                        GenPopAffix(V);
                }
                else
                {
                    EAG.Var[V].Def = true;
                    if (AffixOffset[V] != notApplied)
                    {
                        GenAffixAssign(V);
                        GenHeap(NodeName[Node], n);
                        GenClose;
                        if (EAG.Var[EAG.Var[V].Neg].Def)
                        {
                            output.writeln;
                            GenUnequalPred(EAG.Var[V].Neg, V);
                            --AffixAppls[EAG.Var[V].Neg];
                            --AffixAppls[V];
                            if (UseRefCnt && AffixAppls[V] > 0)
                                GenIncRefCnt(V);
                            if (UseRefCnt)
                                GenFreeAffix(EAG.Var[V].Neg);
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
                GenVar(NodeName[Node1]);
                output.write(" = ");
                GenHeap(NodeName[Node], n);
                output.writeln(";");
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
                && (VisitSeq.GetVisitNo(AP) == VisitNo || IsPred))
        {
            Node = EAG.ParamBuf[SOAG.AffOcc[AP].ParamBufInd].Affixform;
            SN = SymOccInd - SOAG.Rule[SOAG.SymOcc[SymOccInd].RuleInd].SymOcc.Beg;
            if (Node < 0)
            {
                V = -Node;
                if (EAG.Var[V].Def)
                {
                    GenPos(PosNeeded);
                    output.write("Eq(");
                    GenAffPos(S, AN);
                    output.write(", ");
                    GenAffix(V);
                    output.write(", ");
                    GenEqualErrMsg(V);
                    output.writeln(");");
                    --AffixAppls[V];
                    if (UseRefCnt)
                        GenFreeAffix(V);
                    if (Optimize)
                        GenPopAffix(V);
                    if (UseRefCnt)
                    {
                        output.write("FreeHeap(");
                        GenAffPos(S, AN);
                        output.writeln(");");
                    }
                }
                else
                {
                    EAG.Var[V].Def = true;
                    if (!IsPred)
                    {
                        if (AffixOffset[V] != notApplied)
                        {
                            GenAffixAssign(V);
                            GenAffPos(S, AN);
                            GenClose;
                            if (UseRefCnt)
                                output.write(" // komplementäre Referenzzählerbehandlung");
                            output.writeln;
                        }
                    }
                    if (EAG.Var[EAG.Var[V].Neg].Def)
                    {
                        GenPos(PosNeeded);
                        output.write("UnEq(");
                        GenAffix(EAG.Var[V].Neg);
                        output.write(", ");
                        GenAffix(V);
                        output.write(", ");
                        GenEqualErrMsg(V);
                        output.writeln(");");
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
                GenVar(NodeName[Node]);
                output.write(" = ");
                GenAffPos(S, AN);
                output.writeln(";");
                GenAnalTraverse(Node);
                if (UseRefCnt)
                {
                    output.write("FreeHeap(");
                    GenAffPos(S, AN);
                    output.writeln(");");
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
private void GenVisitCall(int SO, int VisitNo) @safe
{
    output.writeln("Visit(TreeAdr + ", SubTreeOffset[SO], ", ", VisitNo, ");");
}

/**
 * SEM: generiert nur Kommentar
 */
private void GenLeave(int VisitNo) @safe
{
    output.writeln("// Leave; VisitNo: ", VisitNo);
}

/**
 * IN: Symbolvorkommen eines Prädikates
 * OUT: -
 * SEM: Generierung des Aufrufes einer Prädikatprozedur
 */
private void GenPredCall(int SO) @safe
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
                    GenIncRefCnt(V);
            }
        }
    }
    S = SOAG.SymOcc[SO].SymInd;
    output.write("Check", S, `("`);
    output.write(EAG.NamedHNontRepr(S));
    output.write(`", `);
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
                        GenAffPos(S, AN);
                    else
                        output.write("GV", -SOAG.StorageName[AP1]);
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
                GenAffPos(S, AN);
            else
                GenAffix(V);
        }
        if (AP != SOAG.SymOcc[SO].AffOcc.End)
            output.write(", ");
        else
            output.writeln(");");
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
                        output.write("Stacks.Push(Stack", SOAG.StorageName[AP1], ", ");
                        GenAffPos(S, AN);
                        output.writeln(");");
                    }
                }
                else if (AffixOffset[V] == notApplied)
                {
                    output.write("FreeHeap(");
                    GenAffPos(S, AN);
                    output.writeln("); // Dummy-Variable");
                }
            }
            else
            {
                --AffixAppls[V];
                if (UseRefCnt)
                    GenFreeAffix(V);
                if (Optimize)
                    GenPopAffix(V);
            }
        }
    }
}

/**
 * IN:  Regel
 * OUT: -
 * SEM: Generierung der Variablendeklarationen einer Regel
 */
private void GenVarDecls(int R) @safe
{
    output.writeln("IndexType TreeAdr;");
    output.writeln("IndexType VI;");
    output.writeln("SemTreeEntry S;");
    if (LocalVars[R] > 0)
    {
        for (int i = 1; i <= LocalVars[R]; ++i)
        {
            output.write("HeapType ");
            GenVar(i);
            output.writeln(";");
        }
    }
}

/**
 * IN:  Regel, Nummer des Visit-Sequenz-Eintrages, Notwendigkeit der Positionszuweisung
 * OUT: -
 * SEM: Generierung der Positionszuweisung vor Prädikatprozeduraufrufen;
 *      zugewiesen wird die Position des vorhergehenden Visits
 */
private void GenPredPos(int R, int i, ref bool PosNeeded) @safe
{
    int k;

    if (PosNeeded)
    {
        --i;
        while (cast(SOAG.Visit) SOAG.VS[i] is null && cast(SOAG.Leave) SOAG.VS[i] is null && i > SOAG.Rule[R].VS.Beg)
            --i;
        if (auto visit = cast(SOAG.Visit) SOAG.VS[i])
            k = SubTreeOffset[visit.SymOcc];
        else
            k = SOAG.Rule[R].SymOcc.Beg;
        output.writeln("Pos = SemTree[TreeAdr + ", k, "].Pos;");
        PosNeeded = false;
    }
}

/**
 * IN: Regelnummer
 * OUT: -
 * SEM: Generiert Code für die Visit-Sequenzen einer Regel
 */
private void GenVisitRule(int R)
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

    output.writeln("void VisitRule", R, "(long Symbol, int VisitNo)");
    output.writeln("/*");
    Protocol.output = output;
    output.write(" * ");
    Protocol.WriteRule(R);
    output.writeln(" */");
    Protocol.output = stdout;
    output.writeln("{");
    GenVarDecls(R);
    NontCnt = 1;
    for (SO = SOAG.Rule[R].SymOcc.Beg + 1; SO <= SOAG.Rule[R].SymOcc.End; ++SO)
        if (!SOAG.IsPredNont(SO))
            ++NontCnt;
    SO = SOAG.Rule[R].SymOcc.Beg;
    output.writeln("if (VisitNo == syntacticPart)");
    output.writeln("{");
    output.writeln("if (NextSemTree >= SemTree.length - ", NontCnt, ") ExpandSemTree;");
    output.writeln("TreeAdr = SemTree[Symbol].Adr;");
    output.writeln("SemTree[Symbol].Adr = NextSemTree;");
    output.writeln("SemTree[Symbol].Pos = PosTree[TreeAdr];");
    output.writeln("AffixVarCount += ", GetAffixCount(R), ";");
    if (AffixVarCount[R] > 0)
    {
        output.writeln("if (NextVar >= Var.length - ", AffixVarCount[R], ") ExpandVar;");
        output.writeln("SemTree[Symbol].VarInd = NextVar; NextVar += ", AffixVarCount[R], ";");
    }
    else
    {
        output.writeln("SemTree[Symbol].VarInd = nil;");
    }
    output.writeln("SemTree[NextSemTree] = SemTree[Symbol];");
    output.writeln("++NextSemTree;");
    for (SO = SOAG.Rule[R].SymOcc.Beg + 1; SO <= SOAG.Rule[R].SymOcc.End; ++SO)
    {
        if (!SOAG.IsPredNont(SO))
        {
            output.writeln("S = new SemTreeEntry;");
            output.writeln("S.Adr = Tree[TreeAdr + ", SubTreeOffset[SO], "];");
            output.writeln("S.Rule = ", FirstRule[SOAG.SymOcc[SO].SymInd] - 1, " + MOD(Tree[S.Adr], hyperArityConst);");
            output.writeln("SemTree[NextSemTree] = S; ++NextSemTree;");
        }
    }
    first = true;
    for (SO = SOAG.Rule[R].SymOcc.Beg + 1; SO <= SOAG.Rule[R].SymOcc.End; ++SO)
    {
        if (!SOAG.IsPredNont(SO))
        {
            if (first)
            {
                output.writeln("TreeAdr = SemTree[Symbol].Adr;");
                first = false;
            }
            output.writeln("Visit(TreeAdr + ", SubTreeOffset[SO], ", syntacticPart);");
        }
    }
    output.writeln("}");
    output.writeln("else");
    output.writeln("{");
    output.writeln("TreeAdr = SemTree[Symbol].Adr;");
    if (AffixVarCount[R] > 0)
        output.writeln("VI = SemTree[Symbol].VarInd;");
    if (VisitSeq.GetMaxVisitNo(SOAG.Rule[R].SymOcc.Beg) == 1)
    {
        onlyoneVisit = true;
    }
    else
    {
        onlyoneVisit = false;
        output.writeln("switch (VisitNo)");
        output.writeln("{");
        output.writeln("case 1:");
    }
    VisitNo = 1;
    PosNeeded = true;
    output.writeln("// Visit-beginnende Analyse");
    GenAnalPred(SOAG.Rule[R].SymOcc.Beg, VisitNo);
    for (i = SOAG.Rule[R].VS.Beg; i <= SOAG.Rule[R].VS.End; ++i)
    {
        if (auto visit = cast(SOAG.Visit) SOAG.VS[i])
        {
            SO = visit.SymOcc;
            S = SOAG.SymOcc[SO].SymInd;
            VN = visit.VisitNo;
            output.writeln("// Synthese");
            GenSynPred(SO, VN);
            GenVisitCall(SO, VN);
            output.writeln("// Analyse");
            GenAnalPred(SO, VN);
            output.writeln;
            PosNeeded = true;
        }
        else if (auto call = cast(SOAG.Call) SOAG.VS[i])
        {
            SO = call.SymOcc;
            output.writeln("// Synthese");
            GenSynPred(SO, -1);
            GenPredPos(R, i, PosNeeded);
            GenPredCall(SO);
            output.writeln("// Analyse");
            GenAnalPred(SO, -1);
            output.writeln;
        }
        else if (auto leave = cast(SOAG.Leave) SOAG.VS[i])
        {
            SO = SOAG.Rule[R].SymOcc.Beg;
            VN = leave.VisitNo;

            assert(VN == VisitNo);

            output.writeln("// Visit-abschließende Synthese");
            GenSynPred(SO, VisitNo);
            GenLeave(VisitNo);
            if (VisitNo < VisitSeq.GetMaxVisitNo(SO))
            {
                output.writeln("break;");
                ++VisitNo;
                PosNeeded = true;
                output.writeln("case ", VisitNo, ":");
                output.writeln("// Visit-beginnende Analyse");
                GenAnalPred(SO, VisitNo);
            }
            else
            {
                if (!onlyoneVisit)
                    output.writeln("break;");
            }
        }
    }
    if (!onlyoneVisit)
    {
        output.writeln("default:");
        output.writeln("assert(0);");
        output.writeln("}");
    }
    output.writeln("}");
    output.writeln("}");
    output.writeln;
}

/**
 * SEM: Generierung der Prozedur 'Visit', die die Besuche auf die entsprechenden Regeln verteilt
 */
private void GenVisit()
{
    output.writeln("void Visit(long Symbol, int VisitNo)");
    output.writeln("{");
    output.writeln("switch (SemTree[Symbol].Rule)");
    output.writeln("{");
    for (int R = SOAG.firstRule; R < SOAG.NextRule; ++R)
    {
        if (SOAG.IsEvaluatorRule(R))
        {
            output.write("case ", R, ": ");
            output.writeln("VisitRule", R, "(Symbol, VisitNo); break;");
        }
    }
    output.writeln("default:");
    output.writeln("assert(0);");
    output.writeln("}");
    output.writeln("}");
    output.writeln;
}

/**
 * SEM: Generierung der Konstanten für den Zugriff auf AffPos[] im generierten Compiler
 */
private void GenConstDeclarations() @safe
{
    for (int S = SOAG.firstSym; S < SOAG.NextSym; ++S)
    {
        output.write("const S", S, " = ");
        output.write(SOAG.Sym[S].AffPos.Beg, "; // ");
        output.write(EAG.HNontRepr(S));
        output.writeln;
    }
}

/**
 * SEM: Generierung der Deklarationen der globalen Variablen und Stacks
 */
private void GenStackDeclarations() @safe
{
    if (optimizer.GlobalVar > 0 || optimizer.StackVar > 0)
    {
        for (int V = optimizer.firstGlobalVar; V <= optimizer.GlobalVar; ++V)
            output.writeln("HeapType GV", V, ";");
        for (int V = optimizer.firstStackVar; V <= optimizer.StackVar; ++V)
            output.writeln("Stacks.Stack Stack", V, ";");
        output.writeln;
    }
}

/**
 * SEM: Generierung der Initialisierungen der Stacks
 */
private void GenStackInit() @safe
{
    if (optimizer.StackVar > 0)
    {
        for (int S = optimizer.firstStackVar; S <= optimizer.StackVar; ++S)
            output.writeln("Stacks.New(Stack", S, ", 8);");
    }
}

/**
 * SEM: Generierung des Compiler-Moduls
 */
private string GenerateModule(Settings settings)
{
    int R;
    Input Fix;
    int StartRule;

    void InclFix(char Term)
    {
        import std.conv : to;
        import std.exception : enforce;

        char c = Fix.front.to!char;

        while (c != Term)
        {
            enforce(c != 0,
                    "error: unexpected end of eSOAG.fix.d");

            output.write(c);
            Fix.popFront;
            c = Fix.front.to!char;
        }
        Fix.popFront;
    }

    enum fixName = "soag.fix.d";
    const name = EAG.BaseName ~ "Eval";
    const fileName = settings.path(name ~ ".d");

    Fix = Input(fixName, import(fixName));
    output = File(fileName, "w");
    SLAGGen.InitGen(output, SLAGGen.sweepPass, settings);
    InclFix('$');
    output.write(name);
    InclFix('$');
    output.write(HyperArity());
    InclFix('$');
    GenConstDeclarations;
    InclFix('$');
    if (Optimize)
        GenStackDeclarations;
    SLAGGen.GenDeclarations(settings);
    InclFix('$');
    SLAGGen.GenPredProcs;
    for (R = SOAG.firstRule; R < SOAG.NextRule; ++R)
    {
        if (SOAG.IsEvaluatorRule(R))
        {
            ComputeNodeNames(R);
            ComputeAffixOffset(R);
            GenVisitRule(R);
        }
    }
    GenVisit;
    EmitGen.GenEmitProc(output, settings);
    InclFix('$');
    output.write(SOAG.NextPartNum);
    InclFix('$');
    if (Optimize)
        GenStackInit;
    StartRule = FirstRule[SOAG.SymOcc[SOAG.Sym[EAG.StartSym].FirstOcc].RuleInd];
    InclFix('$');
    if (StartRule - 1 != 0)
        output.write(StartRule - 1, " + ");
    InclFix('$');
    output.write("S", EAG.StartSym);
    InclFix('$');
    EmitGen.GenEmitCall(output, settings);
    InclFix('$');
    EmitGen.GenShowHeap(output);
    InclFix('$');
    if (Optimize)
        output.write(optimizer.StackVar);
    else
        output.write(0);
    InclFix('$');
    if (Optimize)
        output.write(optimizer.GlobalVar);
    else
        output.write(0);
    InclFix('$');
    output.write(EAG.BaseName);
    output.write("Eval");
    InclFix('$');
    output.flush;
    SLAGGen.FinitGen;
    output.close;
    return fileName;
}

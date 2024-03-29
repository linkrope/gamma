module epsilon.soag.partition;

import EAG = epsilon.eag;
import ALists = epsilon.soag.alists;
import Protocol = epsilon.soag.protocol;
import SOAG = epsilon.soag.soag;
import log;
import runtime;
import std.bitmanip : BitArray;

const unor = -1;
const nil = 0;
const element = 1;
const computeDPandIDP = 1;
const dynTopSort = 2;
const firstVarBuf = 0;
const firstChangeBuf = 0;

struct VarBufDesc
{
    int AffOcc;
    int Sym;
    int Num;
    int VarInd;
}

struct ChangeBufDesc
{
    int RuleInd;
    int AffOccInd1;
    int AffOccInd2;
}

VarBufDesc[] VarBuf;
int NextVarBuf;
ChangeBufDesc[] ChangeBuf;
int NextChangeBuf;
int[][] DS;
int[] Deg;
int Phase;
bool CyclicTDP;
bool OAG;
ALists.AList NUV;
ALists.AList MarkedEdges;
ALists.AList LastCur;
BitArray Cur;
BitArray Leave;
BitArray New;
int Seperator;

void Expand() nothrow @safe
{
    size_t NewLen(size_t ArrayLen)
    {
        assert(ArrayLen < DIV(size_t.max, 2));

        return 2 * ArrayLen + 1;
    }

    if (NextVarBuf >= VarBuf.length)
    {
        auto VarBuf1 = new VarBufDesc[NewLen(VarBuf.length)];

        for (size_t i = firstVarBuf; i < VarBuf.length; ++i)
            VarBuf1[i] = VarBuf[i];
        VarBuf = VarBuf1;
    }
    if (NextChangeBuf >= ChangeBuf.length)
    {
        auto ChangeBuf1 = new ChangeBufDesc[NewLen(ChangeBuf.length)];

        for (size_t i = firstChangeBuf; i < ChangeBuf.length; ++i)
            ChangeBuf1[i] = ChangeBuf[i];
        ChangeBuf = ChangeBuf1;
    }
}

void Push(ref ALists.AList Stack, int S, int A1, int A2) nothrow pure @safe
{
    ALists.Append(Stack, S);
    ALists.Append(Stack, A1);
    ALists.Append(Stack, A2);
}

/**
 * IN:  Regel, zwei Affixparameter
 * OUT: boolscher Wert
 * SEM: Test, ob eine Abhängigkeit zwischen den beiden Affixparametern besteht
 */
bool EdgeInTDP(int R, int A1, int A2) @nogc nothrow
{
    return SOAG.Rule[R].TDP[SOAG.AffOcc[A1].AffOccNum.InRule][SOAG.AffOcc[A2].AffOccNum.InRule];
}

/**
 * IN:  Regel, 2 Affixparameter
 * OUT: -
 * SEM: Fügt ein Tripel in das Feld ChangeBuf ein - Speicherung einer in TDP eingefügten Abhängigkeit.
 */
void AddTDPChange(int R, int AO1, int AO2) nothrow @safe
{
    ChangeBuf[NextChangeBuf].RuleInd = R;
    ChangeBuf[NextChangeBuf].AffOccInd1 = AO1;
    ChangeBuf[NextChangeBuf].AffOccInd2 = AO2;
    ++NextChangeBuf;
    if (NextChangeBuf >= ChangeBuf.length)
        Expand;
}

/**
 * IN:  Index in ChangeBuf
 * OUT: -
 * SEM: Rücksetzen,der in ChangeBuf gespeicherten Abhängigkeiten in den TDP's
 */
void ResetTDPChanges(int End) @nogc nothrow
{
    for (int i = firstChangeBuf; i <= End; ++i)
    {
        SOAG.Rule[ChangeBuf[i].RuleInd].TDP[SOAG.AffOcc[ChangeBuf[i].AffOccInd1].AffOccNum.InRule]
            [SOAG.AffOcc[ChangeBuf[i].AffOccInd2].AffOccNum.InRule] = false;
    }
}

/**
 * IN:  Regel; zwei Affixparameter
 * OUT: -
 * SEM: fügt die Kante (AO1,AO2) in den TDP ein und bildet den transitiven Abschluss TDP+;
 *      die eingefügte Abhängigkeit lautet: AO2 hängt ab von AO1, AO1->AO2 im Sinne des Datenflusses;
 *      markiert alle neu eingefügten Kanten, indem sie auf einen Stack gelegt werden
 * SEF: NUV: AList ist global
 * MarkedEdges falls Phase = computeDPandIDP
 * ChangeBuf, CyclicTDP falls Phase = dynTopSort
 */
void AddTDPTrans(int R, int AO1, int AO2)
{
    int AO3;
    int AO4;
    int AN1;
    int AN2;
    int AN3;
    int AN4;

    ALists.Reset(NUV);
    if (!EdgeInTDP(R, AO1, AO2))
    {
        AN1 = SOAG.AffOcc[AO1].AffOccNum.InRule;
        AN2 = SOAG.AffOcc[AO2].AffOccNum.InRule;
        for (AO4 = SOAG.Rule[R].AffOcc.Beg; AO4 <= SOAG.Rule[R].AffOcc.End; ++AO4)
        {
            AN4 = SOAG.AffOcc[AO4].AffOccNum.InRule;
            if ((AN4 == AN2 || SOAG.Rule[R].TDP[AN2][AN4]) && !SOAG.Rule[R].TDP[AN1][AN4])
                ALists.Append(NUV, AO4);
        }
        for (AO3 = SOAG.Rule[R].AffOcc.Beg; AO3 <= SOAG.Rule[R].AffOcc.End; ++AO3)
        {
            AN3 = SOAG.AffOcc[AO3].AffOccNum.InRule;
            if ((AN3 == AN1 || SOAG.Rule[R].TDP[AN3][AN1]) && !SOAG.Rule[R].TDP[AN3][AN2])
            {
                for (size_t i = ALists.firstIndex; i <= NUV.Last; ++i)
                {
                    AO4 = NUV.Elem[i];
                    if (!EdgeInTDP(R, AO3, AO4))
                    {
                        SOAG.Rule[R].TDP[AN3][SOAG.AffOcc[AO4].AffOccNum.InRule] = true;
                        if (SOAG.AffOcc[AO3].SymOccInd == SOAG.AffOcc[AO4].SymOccInd
                                && !SOAG.IsPredNont(SOAG.AffOcc[AO3].SymOccInd))
                        {
                            Push(MarkedEdges, SOAG.SymOcc[SOAG.AffOcc[AO3].SymOccInd].SymInd,
                                    SOAG.AffOcc[AO3].AffOccNum.InSym,
                                    SOAG.AffOcc[AO4].AffOccNum.InSym);
                        }
                        if (Phase == dynTopSort)
                            AddTDPChange(R, AO3, AO4);
                    }
                }
            }
            if (SOAG.Rule[R].TDP[AN3][AN3])
            {
                if (Phase == computeDPandIDP)
                {
                    Protocol.output.write("...a cyclic affix dependence was found!\n");
                    Protocol.WriteRule(R);
                    Protocol.output.writeln;
                    Protocol.WriteAffOcc(AO3);
                    Protocol.output.writeln;
                    Protocol.output.write("Preorder  of ");
                    Protocol.WriteAffOcc(AO1);
                    Protocol.output.writeln;
                    Protocol.output.write("Postorder of ");
                    Protocol.WriteAffOcc(AO2);
                    Protocol.output.writeln;
                    Protocol.output.writeln;
                    SOAG.Error(SOAG.cyclicTDP, "eSOAGVSGen.AddTDPTrans");
                }
                else if (Phase == dynTopSort)
                {
                    CyclicTDP = true;
                }
            }
        }
    }
}

/**
 * IN:  Affixparameter, Affixform, Affixparameter definierend oder applizierend ?
 * OUT: -
 * SEM: ordnet im Feld VarBuf[] jeder Variablen, die im Baum der Affixform gefunden wird,
 *      den zugehörigen Affixparameter, sowie das Variablensymbol zu
 * SEF: VarBuf[], NextVarBuf
 */
void SetAffOccforVars(int AO, int Affixform, bool isDef) nothrow @safe
{
    int MA;
    if (Affixform < 0)
    {
        if (NextVarBuf + 1 >= VarBuf.length)
            Expand;
        VarBuf[NextVarBuf].AffOcc = AO;
        if (isDef)
            VarBuf[NextVarBuf].Sym = -EAG.Var[-Affixform].Sym;
        else
            VarBuf[NextVarBuf].Sym = EAG.Var[-Affixform].Sym;
        VarBuf[NextVarBuf].Num = EAG.Var[-Affixform].Num;
        VarBuf[NextVarBuf].VarInd = -Affixform;
        ++NextVarBuf;
    }
    else if (EAG.MAlt[EAG.NodeBuf[Affixform]].Arity > 0)
    {
        for (MA = 1; MA <= EAG.MAlt[EAG.NodeBuf[Affixform]].Arity; ++MA)
            SetAffOccforVars(AO, EAG.NodeBuf[Affixform + MA], isDef);
    }
}

/**
 * IN:  Regel
 * OUT: -
 * SEM: berechnet für alle Affixvariablen einer Regel den Affixparameter des zugehörigen definierenden Affixes
 *      und speichert  diesen in DefAffOcc[]
 * SEF: Zugriffe auf VarBuf[]
 */
void ComputeDefAffOcc(int R)
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
    foreach (V; Scope.Beg .. Scope.End)
    {
        bool Found;
        int i = firstVarBuf - 1;

        do
        {
            ++i;
            Found = EAG.Var[V].Sym == -VarBuf[i].Sym && EAG.Var[V].Num == VarBuf[i].Num;
        }
        while (!Found && i < NextVarBuf - 1);
        if (Found)
        {
            SOAG.DefAffOcc[V] = VarBuf[i].AffOcc;
        }
        else
        {
            import std.stdio : writeln;  // TODO: replace with log

            writeln(EAG.Var[V].Pos);
            SOAG.Error(SOAG.notLeftDefined, "epsilon.soag.partition.ComputeDefAffOcc");
        }
    }
}

/**
 * IN:  Regel
 * OUT: -
 * SEM: Berechnet in AffixApplCnt die Anzahl der Applikationen eines Affixes,
 *      außerdem wird für jeden Vergleich eine Abhängigkeit in den DP aufgenommen
 * PRE: DefAffOcc[] muss berechnet sein
 */
void ComputeAffixApplCnt(int R) @nogc nothrow
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
    foreach (A; Scope.Beg .. Scope.End)
    {
        int i = firstVarBuf;

        while (i < NextVarBuf)
        {
            if (EAG.Var[A].Sym == -VarBuf[i].Sym
                    && (EAG.Var[A].Num == VarBuf[i].Num && SOAG.DefAffOcc[A] != VarBuf[i].AffOcc
                        || EAG.Var[A].Num == -VarBuf[i].Num && SOAG.DefAffOcc[VarBuf[i].VarInd] == VarBuf[i].AffOcc))
            {
                const AN = VarBuf[i].AffOcc - SOAG.Rule[R].AffOcc.Beg;
                const DAN = SOAG.DefAffOcc[A] - SOAG.Rule[R].AffOcc.Beg;

                SOAG.Rule[R].DP[DAN][AN] = true;
                ++SOAG.AffixApplCnt[A];
            }
            else if (EAG.Var[A].Sym == VarBuf[i].Sym && EAG.Var[A].Num == VarBuf[i].Num)
            {
                ++SOAG.AffixApplCnt[A];
            }
            ++i;
        }
    }
}

/**
 * SEM: Initialisierung des Abhängigkeitsgraphen für jeden Affixparamter
 *      aller Regeln aus der Spezifikationsdatenstruktur
 * SEF: auf alle globalen DSen
 */
void ComputeDP()
{
    int R;
    int AO;
    int SO;
    int i;
    int j;
    int PBI;
    int FirstSOVar;

    Phase = computeDPandIDP;
    ALists.New(MarkedEdges, 256);
    ALists.New(NUV, 56);
    for (R = SOAG.firstRule; R < SOAG.NextRule; ++R)
    {
        if (SOAG.IsEvaluatorRule(R))
        {
            for (SO = SOAG.Rule[R].SymOcc.Beg; SO <= SOAG.Rule[R].SymOcc.End; ++SO)
            {
                FirstSOVar = NextVarBuf;
                for (AO = SOAG.SymOcc[SO].AffOcc.Beg; AO <= SOAG.SymOcc[SO].AffOcc.End;
                        ++AO)
                {
                    PBI = SOAG.AffOcc[AO].ParamBufInd;
                    SetAffOccforVars(AO, EAG.ParamBuf[PBI].Affixform, EAG.ParamBuf[PBI].isDef);
                }
                if (SOAG.IsPredNont(SO))
                {
                    for (i = FirstSOVar; i < NextVarBuf; ++i)
                    {
                        for (j = FirstSOVar; j < NextVarBuf; ++j)
                        {
                            if (VarBuf[j].Sym < 0 && VarBuf[i].Sym > 0)
                            {
                                AddTDPTrans(R, VarBuf[i].AffOcc, VarBuf[j].AffOcc);
                                SOAG.Rule[R].DP[SOAG.AffOcc[VarBuf[i].AffOcc].AffOccNum.InRule]
                                    [SOAG.AffOcc[VarBuf[j].AffOcc].AffOccNum.InRule] = true;
                            }
                        }
                    }
                }
            }
            ComputeDefAffOcc(R);
            ComputeAffixApplCnt(R);
            if (SOAG.Rule[R].AffOcc.End >= SOAG.Rule[R].AffOcc.Beg)
            {
                for (i = firstVarBuf; i < NextVarBuf; ++i)
                {
                    if (VarBuf[i].Sym > 0)
                    {
                        AddTDPTrans(R, SOAG.DefAffOcc[VarBuf[i].VarInd], VarBuf[i].AffOcc);
                        SOAG.Rule[R].DP[SOAG.AffOcc[SOAG.DefAffOcc[VarBuf[i].VarInd]].AffOccNum.InRule]
                            [SOAG.AffOcc[VarBuf[i].AffOcc].AffOccNum.InRule] = true;
                    }
                }
                NextVarBuf = firstVarBuf;
            }
        }
    }
}

/**
 * SEM: bildet in TDP alle induzierten Abhängigkeiten solange MarkedEdges nicht leer ist
 *      und die Ausgabeinvariante TDP = ind(TDP) gilt.
 * SEF: MarkedEdges, TDP
 */
void ComputeInducedTDP()
{
    int SO;
    int AN1;
    int AN2;
    int AO1;
    int AO2;
    while (MarkedEdges.Last >= ALists.firstIndex)
    {
        AN2 = MarkedEdges.Elem[MarkedEdges.Last];
        ALists.Delete(MarkedEdges, MarkedEdges.Last);
        AN1 = MarkedEdges.Elem[MarkedEdges.Last];
        ALists.Delete(MarkedEdges, MarkedEdges.Last);
        SO = MarkedEdges.Elem[MarkedEdges.Last];
        ALists.Delete(MarkedEdges, MarkedEdges.Last);
        SO = SOAG.Sym[SO].FirstOcc;
        while (SO != SOAG.nil)
        {
            AO1 = SOAG.SymOcc[SO].AffOcc.Beg + AN1;
            AO2 = SOAG.SymOcc[SO].AffOcc.Beg + AN2;
            AddTDPTrans(SOAG.SymOcc[SO].RuleInd, AO1, AO2);
            SO = SOAG.SymOcc[SO].Next;
        }
    }
}

/**
 * SEM: bildet in TDP alle induzierten Abhängigkeiten solange MarkedEdges nicht leer ist
 *      und die Ausgabeinvariante TDP = ind(TDP) gilt, damit ist dann TDP = IDP+
 * SEF: -
 */
void ComputeIDPTrans()
{
    ComputeInducedTDP;
}

/**
 * IN:  Affixpositionsnummern a und b, Symbol
 * OUT: Liste von Paaren von Affixpositionsnummern des Symbols X
 * SEM: findet für zwei Affixpositionen eines Symbols eine Orientierung,
 *      fügt diese in alle Regelabhängigkeitsgraphen ein und liefert die Liste
 *      aller bei der transitiven Vervollständigung neu entstandenen Abhängigkeiten zurück
 * SEF: auf ChangeBuf[]
 */
void Orient(int a, int b, int X, ref BitArray New)
{
    int SO;
    int i;
    int a1;
    int b1;
    int AO1;
    int AO2;

    New[] = false;
    CyclicTDP = false;
    NextChangeBuf = firstChangeBuf;
    SO = SOAG.Sym[X].FirstOcc;
    AddTDPTrans(SOAG.SymOcc[SO].RuleInd, SOAG.SymOcc[SO].AffOcc.Beg + b,
            SOAG.SymOcc[SO].AffOcc.Beg + a);
    ComputeInducedTDP;
    if (CyclicTDP)
    {
        CyclicTDP = false;
        OAG = false;
        ResetTDPChanges(NextChangeBuf - 1);
        NextChangeBuf = firstChangeBuf;
        AddTDPTrans(SOAG.SymOcc[SO].RuleInd, SOAG.SymOcc[SO].AffOcc.Beg + a,
                SOAG.SymOcc[SO].AffOcc.Beg + b);
        ComputeInducedTDP;
    }
    if (CyclicTDP)
    {
        error!"grammar is not SOAG";
        SOAG.Error(SOAG.cyclicTDP, "eSOAGVSGen.Orient");
    }
    for (i = firstChangeBuf; i < NextChangeBuf; ++i)
    {
        AO1 = ChangeBuf[i].AffOccInd1;
        AO2 = ChangeBuf[i].AffOccInd2;
        if (SOAG.AffOcc[AO1].SymOccInd == SOAG.AffOcc[AO2].SymOccInd
                && SOAG.SymOcc[SOAG.AffOcc[AO1].SymOccInd].SymInd == X)
        {
            a1 = SOAG.AffOcc[AO1].AffOccNum.InSym;
            b1 = SOAG.AffOcc[AO2].AffOccNum.InSym;
            if (SOAG.IsOrientable(X, a1, b1))
                New[a1 * Seperator + b1] = true;
        }
    }
}

/**
 * IN:  Symbol
 * OUT: -
 * SEM: dynamisches topologisches Sortieren der Affxipositionsabhängigkeiten
 *      unter Heranführung an eine erfolgreiche bzw. unmittelbar erfolgreiche Orientierung
 * SEF: DS[][]
 */
void DynTopSortSym(int X)
{
    import std.conv : to;

    int XmaxAff;
    int AO1;
    int AO2;
    int SO;
    int Part = 0;
    int a1;
    int a;
    int b;
    int c;
    int d;

    XmaxAff = SOAG.SymOcc[SOAG.Sym[X].FirstOcc].AffOcc.End - SOAG.SymOcc[SOAG.Sym[X].FirstOcc].AffOcc.Beg;
    for (a = 0; a <= XmaxAff; ++a)
        for (b = 0; b <= XmaxAff; ++b)
            DS[a][b] = nil;
    SO = SOAG.Sym[X].FirstOcc;
    while (SO != SOAG.nil)
    {
        for (AO1 = SOAG.SymOcc[SO].AffOcc.Beg; AO1 <= SOAG.SymOcc[SO].AffOcc.End; ++AO1)
        {
            for (AO2 = SOAG.SymOcc[SO].AffOcc.Beg; AO2 <= SOAG.SymOcc[SO].AffOcc.End; ++AO2)
            {
                if (EdgeInTDP(SOAG.SymOcc[SO].RuleInd, AO1, AO2))
                {
                    a = SOAG.AffOcc[AO1].AffOccNum.InSym;
                    b = SOAG.AffOcc[AO2].AffOccNum.InSym;
                    if (SOAG.IsOrientable(X, a, b))
                        DS[a][b] = element;
                }
            }
        }
        SO = SOAG.SymOcc[SO].Next;
    }
    for (a = 0; a <= XmaxAff; ++a)
    {
        Deg[a] = 0;
        for (b = 0; b <= XmaxAff; ++b)
        {
            if (DS[a][b] == element)
            {
                ++Deg[a];
            }
            else if (DS[b][a] == nil && SOAG.IsOrientable(X, a, b))
            {
                DS[a][b] = unor;
                DS[b][a] = unor;
            }
        }
    }
    Cur[] = false;
    Leave[] = false;
    for (a = 0; a <= XmaxAff; ++a)
    {
        if (Deg[a] == 0)
        {
            if (SOAG.IsSynthesized(X, a))
                Cur[a] = true;
            else if (SOAG.IsInherited(X, a))
                Leave[a] = true;
        }
    }
    trace!"compute partition for symbol %s"(EAG.HNontRepr(X));
    trace!"initially: Cur=%s, Leave=%s"(Cur, Leave);
    do
    {
        ALists.Reset(LastCur);
        foreach (size_t elem; Cur.bitsSet)
            ALists.Append(LastCur, elem.to!int);
        for (b = 0; b <= XmaxAff; ++b)
        {
            for (a1 = ALists.firstIndex; a1 <= LastCur.Last; ++a1)
            {
                a = LastCur.Elem[a1];
                if (Cur[a] && DS[a][b] == unor)
                {
                    Orient(a, b, X, New);
                    foreach (size_t elem; New.bitsSet)
                    {
                        c = DIV(elem, Seperator).to!int;
                        d = MOD(elem, Seperator).to!int;
                        DS[c][d] = element;
                        ++Deg[c];
                        if (DS[d][c] == unor)
                            DS[d][c] = nil;
                        if (Cur[c])
                            Cur[c] = false;
                        else if (Deg[c] == 1)
                            Leave[c] = false;
                    }
                }
            }
        }
        ++Part;
        trace!"partition %s: Cur=%s, Leave=%s"(Part, Cur, Leave);
        foreach (size_t elem; Cur.bitsSet)
        {
            SOAG.PartNum[SOAG.Sym[X].AffPos.Beg + elem] = Part;
            for (b = 0; b <= XmaxAff; ++b)
            {
                if (DS[b][elem] == element)
                {
                    --Deg[b];
                    if (Deg[b] == 0)
                        Leave[b] = true;
                }
            }
        }
        trace!"afterwards: Cur=%s, Leave=%s"(Cur, Leave);

        BitArray tmp = Cur;

        Cur = Leave;
        Leave = tmp;
        Leave[] = false;
    }
    while (Cur.count > 0);
    if (SOAG.Sym[X].MaxPart < Part)
        SOAG.Sym[X].MaxPart = Part;
    if (SOAG.MaxPart < Part)
        SOAG.MaxPart = Part;
}

/**
 * SEM: dynamisches topologisches Sortieren aller Symbole der Grammatik
 */
void DynTopSort()
{
    Cur = BitArray();
    Cur.length = SOAG.MaxAffNumInSym + 1;
    Leave = BitArray();
    Leave.length = SOAG.MaxAffNumInSym + 1;
    Deg = new int[SOAG.MaxAffNumInSym + 1];
    DS = new int[][SOAG.MaxAffNumInSym + 1];
    foreach (ref row; DS)
        row = new int[SOAG.MaxAffNumInSym + 1];
    New = BitArray();
    New.length = (SOAG.MaxAffNumInSym + 1) * (SOAG.MaxAffNumInSym + 1) + 1;
    Seperator = SOAG.MaxAffNumInSym + 1;
    ALists.New(LastCur, 16);
    for (int S = EAG.firstHNont; S < EAG.NextHNont; ++S)
    {
        if (!EAG.Pred[S] && EAG.All[S])
            DynTopSortSym(S);
    }
}

/**
 * SEM: Treiber
 */
void Compute()
{
    const undefined = -1;

    SOAG.Init;
    // initialize partition number of each affix position to finally enforce that it's defined
    SOAG.PartNum[SOAG.firstPartNum .. SOAG.NextPartNum] = undefined;
    VarBuf = new VarBufDesc[50];
    ChangeBuf = new ChangeBufDesc[64];
    NextVarBuf = firstVarBuf;
    NextChangeBuf = firstChangeBuf;
    OAG = true;
    Phase = computeDPandIDP;
    ComputeDP;
    ComputeIDPTrans;
    Phase = dynTopSort;
    DynTopSort;
    if (OAG)
        info!"grammar is SOAG";
    else
        info!"grammar is SOAG (backtracked)";
}

module soag.eSOAGPartition;

import runtime;
import EAG = eEAG;
import SOAG = soag.eSOAG;
import Sets = eSets;
import ALists = soag.eALists;
import IO = eIO;
import Protocol = soag.eSOAGProtocol;
import ASets = soag.eASets;
import BSets = soag.eBSets;
import std.stdio;

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
alias OpenVarBuf = VarBufDesc[];

struct ChangeBufDesc
{
    int RuleInd;
    int AffOccInd1;
    int AffOccInd2;
}
alias OpenChangeBuf = ChangeBufDesc[];

OpenVarBuf VarBuf;
int NextVarBuf;
OpenChangeBuf ChangeBuf;
int NextChangeBuf;
int[][] DS;
int[] Deg;
int Phase;
bool CyclicTDP;
bool OEAG;
ALists.AList NUV;
ALists.AList MarkedEdges;
ALists.AList LastCur;
ASets.ASet Cur;
ASets.ASet Leave;
BSets.BSet New;
int Seperator;

void Expand()
{
    OpenVarBuf VarBuf1;
    OpenChangeBuf ChangeBuf1;
    long i;
    long NewLen(long ArrayLen)
    {
        if (ArrayLen < DIV(int.max, 2))
        {
            return 2 * ArrayLen + 1;
        }
        else
        {
            assert(0);
        }
    }

    if (NextVarBuf >= VarBuf.length)
    {
        NEW(VarBuf1, NewLen(VarBuf.length));
        for (i = firstVarBuf; i <= VarBuf.length - 1; ++i)
        {
            VarBuf1[i] = VarBuf[i];
        }
        VarBuf = VarBuf1;
    }
    if (NextChangeBuf >= ChangeBuf.length)
    {
        NEW(ChangeBuf1, NewLen(ChangeBuf.length));
        for (i = firstChangeBuf; i <= ChangeBuf.length - 1; ++i)
        {
            ChangeBuf1[i] = ChangeBuf[i];
        }
        ChangeBuf = ChangeBuf1;
    }
}

void Push(ref ALists.AList Stack, int S, int A1, int A2)
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
bool EdgeInTDP(int R, int A1, int A2)
{
    return Sets.In(SOAG.Rule[R].TDP[SOAG.AffOcc[A1].AffOccNum.InRule],
            SOAG.AffOcc[A2].AffOccNum.InRule);
}

/**
 * IN:  Regel, 2 Affixparameter
 * OUT: -
 * SEM: Fügt ein Tripel in das Feld ChangeBuf ein - Speicherung einer in TDP eingefügten Abhängigkeit.
 */
void AddTDPChange(int R, int AO1, int AO2)
{
    ChangeBuf[NextChangeBuf].RuleInd = R;
    ChangeBuf[NextChangeBuf].AffOccInd1 = AO1;
    ChangeBuf[NextChangeBuf].AffOccInd2 = AO2;
    ++NextChangeBuf;
    if (NextChangeBuf >= ChangeBuf.length)
    {
        Expand;
    }
}

/**
 * IN:  Index in ChangeBuf
 * OUT: -
 * SEM: Rücksetzen,der in ChangeBuf gespeicherten Abhängigkeiten in den TDP's
 */
void ResetTDPChanges(int End)
{
    int i;
    for (i = firstChangeBuf; i <= End; ++i)
    {
        Sets.Excl(
                SOAG.Rule[ChangeBuf[i].RuleInd].TDP[SOAG.AffOcc[ChangeBuf[i].AffOccInd1].AffOccNum.InRule],
                SOAG.AffOcc[ChangeBuf[i].AffOccInd2].AffOccNum.InRule);
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
    int i;
    ALists.Reset(NUV);
    if (!EdgeInTDP(R, AO1, AO2))
    {
        AN1 = SOAG.AffOcc[AO1].AffOccNum.InRule;
        AN2 = SOAG.AffOcc[AO2].AffOccNum.InRule;
        for (AO4 = SOAG.Rule[R].AffOcc.Beg; AO4 <= SOAG.Rule[R].AffOcc.End; ++AO4)
        {
            AN4 = SOAG.AffOcc[AO4].AffOccNum.InRule;
            if ((AN4 == AN2 || Sets.In(SOAG.Rule[R].TDP[AN2], AN4))
                    && !Sets.In(SOAG.Rule[R].TDP[AN1], AN4))
            {
                ALists.Append(NUV, AO4);
            }
        }
        for (AO3 = SOAG.Rule[R].AffOcc.Beg; AO3 <= SOAG.Rule[R].AffOcc.End; ++AO3)
        {
            AN3 = SOAG.AffOcc[AO3].AffOccNum.InRule;
            if ((AN3 == AN1 || Sets.In(SOAG.Rule[R].TDP[AN3], AN1))
                    && !Sets.In(SOAG.Rule[R].TDP[AN3], AN2))
            {
                for (i = ALists.firstIndex; i <= NUV.Last; ++i)
                {
                    AO4 = NUV.Elem[i];
                    if (!EdgeInTDP(R, AO3, AO4))
                    {
                        Sets.Incl(SOAG.Rule[R].TDP[AN3], SOAG.AffOcc[AO4].AffOccNum.InRule);
                        if (SOAG.AffOcc[AO3].SymOccInd == SOAG.AffOcc[AO4].SymOccInd
                                && !SOAG.IsPredNont(SOAG.AffOcc[AO3].SymOccInd))
                        {
                            Push(MarkedEdges, SOAG.SymOcc[SOAG.AffOcc[AO3].SymOccInd].SymInd,
                                    SOAG.AffOcc[AO3].AffOccNum.InSym,
                                    SOAG.AffOcc[AO4].AffOccNum.InSym);
                        }
                        if (Phase == dynTopSort)
                        {
                            AddTDPChange(R, AO3, AO4);
                        }
                    }
                }
            }
            if (Sets.In(SOAG.Rule[R].TDP[AN3], AN3))
            {
                if (Phase == computeDPandIDP)
                {
                    IO.WriteText(Protocol.Out, "...a cyclic affix dependence was found!\n");
                    Protocol.WriteRule(R);
                    IO.WriteLn(Protocol.Out);
                    Protocol.WriteAffOcc(AO3);
                    IO.WriteLn(Protocol.Out);
                    IO.WriteString(Protocol.Out, "Preorder  of ");
                    Protocol.WriteAffOcc(AO1);
                    IO.WriteLn(Protocol.Out);
                    IO.WriteString(Protocol.Out, "Postorder of ");
                    Protocol.WriteAffOcc(AO2);
                    IO.WriteLn(Protocol.Out);
                    IO.WriteLn(Protocol.Out);
                    IO.Update(Protocol.Out);
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
void SetAffOccforVars(int AO, int Affixform, bool isDef)
{
    int MA;
    if (Affixform < 0)
    {
        if (NextVarBuf + 1 >= VarBuf.length)
        {
            Expand;
        }
        VarBuf[NextVarBuf].AffOcc = AO;
        if (isDef)
        {
            VarBuf[NextVarBuf].Sym = -EAG.Var[-Affixform].Sym;
        }
        else
        {
            VarBuf[NextVarBuf].Sym = EAG.Var[-Affixform].Sym;
        }
        VarBuf[NextVarBuf].Num = EAG.Var[-Affixform].Num;
        VarBuf[NextVarBuf].VarInd = -Affixform;
        ++NextVarBuf;
    }
    else if (EAG.MAlt[EAG.NodeBuf[Affixform]].Arity > 0)
    {
        for (MA = 1; MA <= EAG.MAlt[EAG.NodeBuf[Affixform]].Arity; ++MA)
        {
            SetAffOccforVars(AO, EAG.NodeBuf[Affixform + MA], isDef);
        }
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
    EAG.Rule EAGRule;
    int V;
    int i;
    bool Found;
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
        i = firstVarBuf - 1;
        do
        {
            ++i;
            Found = EAG.Var[V].Sym == -VarBuf[i].Sym && EAG.Var[V].Num == VarBuf[i].Num;
        }
        while (!(Found || i >= NextVarBuf - 1));
        if (Found)
        {
            SOAG.DefAffOcc[V] = VarBuf[i].AffOcc;
        }
        else
        {
            writeln(EAG.Var[V].Pos);
            SOAG.Error(SOAG.notLeftDefined, "eSOAGPartition.ComputeDefAffOcc");
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
void ComputeAffixApplCnt(int R)
{
    EAG.ScopeDesc Scope;
    EAG.Rule EAGRule;
    int A;
    int AN;
    int DAN;
    int i;
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
    for (A = Scope.Beg; A <= Scope.End - 1; ++A)
    {
        i = firstVarBuf;
        while (i < NextVarBuf)
        {
            if (EAG.Var[A].Sym == -VarBuf[i].Sym
                    && (EAG.Var[A].Num == VarBuf[i].Num
                        && SOAG.DefAffOcc[A] != VarBuf[i].AffOcc
                        || EAG.Var[A].Num == -VarBuf[i].Num
                        && SOAG.DefAffOcc[VarBuf[i].VarInd] == VarBuf[i].AffOcc))
            {
                AN = VarBuf[i].AffOcc - SOAG.Rule[R].AffOcc.Beg;
                DAN = SOAG.DefAffOcc[A] - SOAG.Rule[R].AffOcc.Beg;
                Sets.Incl(SOAG.Rule[R].DP[DAN], AN);
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
    EAG.Alt Alt;
    Phase = computeDPandIDP;
    ALists.New(MarkedEdges, 256);
    ALists.New(NUV, 56);
    for (R = SOAG.firstRule; R <= SOAG.NextRule - 1; ++R)
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
                    for (i = FirstSOVar; i <= NextVarBuf - 1; ++i)
                    {
                        for (j = FirstSOVar; j <= NextVarBuf - 1; ++j)
                        {
                            if (VarBuf[j].Sym < 0 && VarBuf[i].Sym > 0)
                            {
                                AddTDPTrans(R, VarBuf[i].AffOcc, VarBuf[j].AffOcc);
                                Sets.Incl(SOAG.Rule[R].DP[SOAG.AffOcc[VarBuf[i].AffOcc].AffOccNum.InRule],
                                        SOAG.AffOcc[VarBuf[j].AffOcc].AffOccNum.InRule);
                            }
                        }
                    }
                }
            }
            ComputeDefAffOcc(R);
            ComputeAffixApplCnt(R);
            if (SOAG.Rule[R].AffOcc.End >= SOAG.Rule[R].AffOcc.Beg)
            {
                for (i = firstVarBuf; i <= NextVarBuf - 1; ++i)
                {
                    if (VarBuf[i].Sym > 0)
                    {
                        AddTDPTrans(R, SOAG.DefAffOcc[VarBuf[i].VarInd], VarBuf[i].AffOcc);
                        Sets.Incl(
                                SOAG.Rule[R].DP[SOAG.AffOcc[SOAG.DefAffOcc[VarBuf[i].VarInd]].AffOccNum.InRule],
                                SOAG.AffOcc[VarBuf[i].AffOcc].AffOccNum.InRule);
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
void Orient(int a, int b, int X, ref BSets.BSet New)
{
    int SO;
    int i;
    int a1;
    int b1;
    int AO1;
    int AO2;
    BSets.Reset(New);
    CyclicTDP = false;
    NextChangeBuf = firstChangeBuf;
    SO = SOAG.Sym[X].FirstOcc;
    AddTDPTrans(SOAG.SymOcc[SO].RuleInd, SOAG.SymOcc[SO].AffOcc.Beg + b,
            SOAG.SymOcc[SO].AffOcc.Beg + a);
    ComputeInducedTDP;
    if (CyclicTDP)
    {
        CyclicTDP = false;
        OEAG = false;
        ResetTDPChanges(NextChangeBuf - 1);
        NextChangeBuf = firstChangeBuf;
        AddTDPTrans(SOAG.SymOcc[SO].RuleInd, SOAG.SymOcc[SO].AffOcc.Beg + a,
                SOAG.SymOcc[SO].AffOcc.Beg + b);
        ComputeInducedTDP;
    }
    if (CyclicTDP)
    {
        IO.WriteText(IO.Msg, "\tGarmmar is not SOAG\n");
        SOAG.Error(SOAG.cyclicTDP, "eSOAGVSGen.Orient");
    }
    for (i = firstChangeBuf; i <= NextChangeBuf - 1; ++i)
    {
        AO1 = ChangeBuf[i].AffOccInd1;
        AO2 = ChangeBuf[i].AffOccInd2;
        if (SOAG.AffOcc[AO1].SymOccInd == SOAG.AffOcc[AO2].SymOccInd
                && SOAG.SymOcc[SOAG.AffOcc[AO1].SymOccInd].SymInd == X)
        {
            a1 = SOAG.AffOcc[AO1].AffOccNum.InSym;
            b1 = SOAG.AffOcc[AO2].AffOccNum.InSym;
            if (SOAG.IsOrientable(X, a1, b1))
            {
                BSets.Insert(New, a1 * Seperator + b1);
            }
        }
    }
}

void WriteDS(int XmaxAff)
{
    int i;
    int j;
    for (i = 0; i <= XmaxAff; ++i)
    {
        IO.WriteText(IO.Msg, "Zeile ");
        IO.WriteInt(IO.Msg, i);
        for (j = 0; j <= XmaxAff; ++j)
        {
            IO.WriteInt(IO.Msg, DS[i][j]);
            IO.WriteString(IO.Msg, " ");
        }
        IO.WriteLn(IO.Msg);
    }
    IO.Update(IO.Msg);
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
    int Part;
    int i;
    int a1;
    int a;
    int b;
    int c;
    int d;
    ASets.ASet tmp;
    Part = 0;
    XmaxAff = SOAG.SymOcc[SOAG.Sym[X].FirstOcc].AffOcc.End
        - SOAG.SymOcc[SOAG.Sym[X].FirstOcc].AffOcc.Beg;
    for (a = 0; a <= XmaxAff; ++a)
    {
        for (b = 0; b <= XmaxAff; ++b)
        {
            DS[a][b] = nil;
        }
    }
    SO = SOAG.Sym[X].FirstOcc;
    while (SO != SOAG.nil)
    {
        for (AO1 = SOAG.SymOcc[SO].AffOcc.Beg; AO1 <= SOAG.SymOcc[SO].AffOcc.End;
                ++AO1)
        {
            for (AO2 = SOAG.SymOcc[SO].AffOcc.Beg; AO2 <= SOAG.SymOcc[SO].AffOcc.End;
                    ++AO2)
            {
                if (EdgeInTDP(SOAG.SymOcc[SO].RuleInd, AO1, AO2))
                {
                    a = SOAG.AffOcc[AO1].AffOccNum.InSym;
                    b = SOAG.AffOcc[AO2].AffOccNum.InSym;
                    if (SOAG.IsOrientable(X, a, b))
                    {
                        DS[a][b] = element;
                    }
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
    ASets.Reset(Cur);
    ASets.Reset(Leave);
    for (a = 0; a <= XmaxAff; ++a)
    {
        if (Deg[a] == 0)
        {
            if (SOAG.IsSynthesized(X, a))
            {
                ASets.Insert(Cur, a);
            }
            else if (SOAG.IsInherited(X, a))
            {
                ASets.Insert(Leave, a);
            }
        }
    }
    do
    {
        ALists.Reset(LastCur);
        for (a = ASets.firstIndex; a <= Cur.List.Last; ++a)
        {
            ALists.Append(LastCur, Cur.List.Elem[a]);
        }
        for (b = 0; b <= XmaxAff; ++b)
        {
            for (a1 = ALists.firstIndex; a1 <= LastCur.Last; ++a1)
            {
                a = LastCur.Elem[a1];
                if (ASets.In(Cur, a) && DS[a][b] == unor)
                {
                    Orient(a, b, X, New);
                    for (i = BSets.firstIndex; i <= New.List.Last; ++i)
                    {
                        c = DIV(New.List.Elem[i], Seperator).to!int;
                        d = MOD(New.List.Elem[i], Seperator).to!int;
                        DS[c][d] = element;
                        ++Deg[c];
                        if (DS[d][c] == unor)
                        {
                            DS[d][c] = nil;
                        }
                        if (ASets.In(Cur, c))
                        {
                            ASets.Delete(Cur, c);
                        }
                        else if (Deg[c] == 1)
                        {
                            ASets.Delete(Leave, c);
                        }
                    }
                }
            }
        }
        ++Part;
        for (a = ASets.firstIndex; a <= Cur.List.Last; ++a)
        {
            SOAG.PartNum[SOAG.Sym[X].AffPos.Beg + Cur.List.Elem[a]] = Part;
            for (b = 0; b <= XmaxAff; ++b)
            {
                if (DS[b][Cur.List.Elem[a]] == element)
                {
                    --Deg[b];
                    if (Deg[b] == 0)
                    {
                        ASets.Insert(Leave, b);
                    }
                }
            }
        }
        tmp = Cur;
        Cur = Leave;
        Leave = tmp;
        ASets.Reset(Leave);
    }
    while (!ASets.IsEmpty(Cur));
    if (SOAG.Sym[X].MaxPart < Part)
    {
        SOAG.Sym[X].MaxPart = Part;
    }
    if (SOAG.MaxPart < Part)
    {
        SOAG.MaxPart = Part;
    }
}

/**
 * SEM: dynamisches topologisches Sortieren aller Symbole der Grammatik
 */
void DynTopSort()
{
    int S;
    ASets.New(Cur, SOAG.MaxAffNumInSym + 1);
    ASets.New(Leave, SOAG.MaxAffNumInSym + 1);
    NEW(Deg, SOAG.MaxAffNumInSym + 1);
    NEW(DS, SOAG.MaxAffNumInSym + 1, SOAG.MaxAffNumInSym + 1);
    BSets.New(New, (SOAG.MaxAffNumInSym + 1) * (SOAG.MaxAffNumInSym + 1));
    Seperator = SOAG.MaxAffNumInSym + 1;
    ALists.New(LastCur, 16);
    for (S = EAG.firstHNont; S <= EAG.NextHNont - 1; ++S)
    {
        if (!Sets.In(EAG.Pred, S) && Sets.In(EAG.All, S))
        {
            DynTopSortSym(S);
        }
    }
}

/**
 * SEM: Treiber
 */
void Compute()
{
    int i;
    SOAG.Init;
    NEW(VarBuf, 50);
    NEW(ChangeBuf, 64);
    NextVarBuf = firstVarBuf;
    NextChangeBuf = firstChangeBuf;
    OEAG = true;
    Phase = computeDPandIDP;
    ComputeDP;
    ComputeIDPTrans;
    Phase = dynTopSort;
    DynTopSort;
    if (OEAG)
    {
        IO.WriteText(IO.Msg, "\n\tGrammar is SOEAG\n");
    }
    else
    {
        IO.WriteText(IO.Msg, "\n\tGrammar is SOEAG (backtracked)\n");
    }
}

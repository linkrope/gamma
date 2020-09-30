module soag.eSOAGOptimizer;

import EAG = eEAG;
import IO = eIO;
import Sets = eSets;
import runtime;
import ALists = soag.eALists;
import SOAG = soag.eSOAG;
import Protocol = soag.eSOAGProtocol;
import SOAGVisitSeq = soag.eSOAGVisitSeq;

const firstGlobalVar = 1;
const firstStackVar = 1;
int GlobalVar;
int StackVar;
SOAG.OpenInteger PN;
bool admissible;
bool disjoint;
ALists.AList VDS;
ALists.AList VS;

/**
 * IN:  Tripel
 * OUT: -
 * SEM: bed. Einfügen des Tripels in die modulglobale Liste VDS, die als Menge interpretiert wird,
 *      deshalb wird das Tripel nur dann eingefügt, wenn es nicht schon Bestandteil der Liste ist.
 */
void IncludeVDS(int S, int VN1, int VN2)
{
    int i = ALists.firstIndex;
    bool notisElement = true;

    while (i < VDS.Last && notisElement)
    {
        notisElement = VDS.Elem[i] != S || VDS.Elem[i + 1] != VN1 || VDS.Elem[i + 2] != VN2;
        i += 3;
    }
    if (notisElement)
    {
        ALists.Append(VDS, S);
        ALists.Append(VDS, VN1);
        ALists.Append(VDS, VN2);
    }
}

void WriteVDS()
{
    IO.Msg.write("Inhalt VDS:\n");
    for (size_t i = ALists.firstIndex; i <= VDS.Last; i += 3)
    {
        IO.Msg.write(EAG.HNontRepr(VDS.Elem[i]));
        IO.Msg.write(", ");
        IO.Msg.write(VDS.Elem[i + 1]);
        IO.Msg.write(", ");
        IO.Msg.write(VDS.Elem[i + 2]);
        IO.Msg.writeln;
        IO.Msg.flush;
    }
}

/**
 * IN:  Tupel
 * OUT: -
 * SEM: bed. Einfügen des Tupels in die modulglobale Liste VS, die als Menge interpretiert wird,
 *      deshalb wird das Tupel nur dann eingefügt, wenn es nicht schon Bestandteil der Liste ist.
 */
void IncludeVS(int S, int VN)
{
    int i = ALists.firstIndex;
    bool notisElement = true;

    while (i < VS.Last && notisElement)
    {
        notisElement = VS.Elem[i] != S || VS.Elem[i + 1] != VN;
        i += 2;
    }
    if (notisElement)
    {
        ALists.Append(VS, S);
        ALists.Append(VS, VN);
    }
}

void WriteVS()
{
    IO.Msg.write("Inhalt VS:\n");
    for (size_t i = ALists.firstIndex; i <= VS.Last; i += 2)
    {
        IO.Msg.write(EAG.HNontRepr(VS.Elem[i]));
        IO.Msg.write(", ");
        IO.Msg.write(VS.Elem[i + 1]);
        IO.Msg.writeln;
        IO.Msg.flush;
    }
}

/**
 * IN:  Regel, Affixparameter
 * OUT: Plannummer
 * SEM: Ermittelt die Nummer des Visitplanes, während dessen Auswertung der Affixparameter berechnet wird
 */
int GetPlanNo(int R, int AP)
{
    int SO;
    int VN;
    SO = SOAG.AffOcc[AP].SymOccInd;
    if (SO == SOAG.Rule[R].SymOcc.Beg)
    {
        return SOAGVisitSeq.GetVisitNo(AP);
    }
    else
    {
        VN = SOAGVisitSeq.GetVisitNo(AP);
        return PN[SOAGVisitSeq.GetVisit(R, SO, VN)];
    }
}

/**
 * IN:  Regel, Affixparameter
 * OUT: Position in der virtuellen extended visit sequence (EVS)
 * SEM: Ermittelt der Position des Affixparameter in der EVS (entspricht set(a) aus der Theorie)
 */
int GetEVSPosforAffOcc(int R, int AP)
{
    int SO = SOAG.AffOcc[AP].SymOccInd;
    int VN = SOAGVisitSeq.GetVisitNo(AP);
    const S = SOAG.SymOcc[SO].SymInd;
    const AN = SOAG.AffOcc[AP].AffOccNum.InSym;
    int V;

    if (SO == SOAG.Rule[R].SymOcc.Beg && SOAG.IsInherited(S, AN))
    {
        if (VN == 1)
        {
            return 0;
        }
        else
        {
            V = SOAGVisitSeq.GetVisit(R, SO, VN - 1);
            return V * 3 + 1;
        }
    }
    V = SOAGVisitSeq.GetVisit(R, SO, VN);
    if (SOAG.IsInherited(S, AN))
    {
        return V * 3 + 1;
    }
    else
    {
        return V * 3 + 3;
    }
}

/**
 * IN:  Regel, Symbolvorkommen, Visit-Nummer
 * OUT: Position in der virtuellen extended visit sequence (EVS)
 * SEM: Ermittelt der Position des durch Symbolvorkommen und Visitnummer eindeutig gekennzeichneten Visits
 *      in der EVS (entspricht visit(j,m) aus der Theorie)
 */
int GetEVSPosforVisit(int R, int SO, int VN)
{
    const V = SOAGVisitSeq.GetVisit(R, SO, VN);

    return V * 3 + 2;
}

/**
 * SEM: Initialisierung der Struktur PN - Berechnung der Plannummer jedes Visits
 */
void Init()
{
    int R;
    int V;
    int PlanNo;

    PN = new int[SOAG.NextVS];
    for (R = SOAG.firstRule; R < SOAG.NextRule; ++R)
    {
        PlanNo = 1;
        for (V = SOAG.Rule[R].VS.Beg; V <= SOAG.Rule[R].VS.End; ++V)
        {
            PN[V] = PlanNo;
            if (cast(SOAG.Leave) SOAG.VS[V] !is null)
            {
                ++PlanNo;
            }
        }
    }
    SOAG.StorageName = new int[SOAG.NextPartNum];
    SOAG.NextStorageName = SOAG.NextPartNum;
    for (V = SOAG.firstStorageName; V < SOAG.NextStorageName; ++V)
    {
        SOAG.StorageName[V] = 0;
    }
    ALists.New(VDS, 16);
    ALists.New(VS, 16);
}

/**
* IN:  Symbol, Affixpositionsnummer
* OUT: -
* SEM: Initialisierung der Mengen VDS und VS für eine Affixposition (analog Step 1 Theorie)
*/
void InitVDSandVS(int S, int A)
{
    int SO;
    int AP;
    int PN;
    int R;
    int RS;
    int AP1;
    int PN1;
    int AN;
    int AN1;

    ALists.Reset(VDS);
    ALists.Reset(VS);
    SO = SOAG.Sym[S].FirstOcc;
    while (SO != SOAG.nil)
    {
        AP = SOAG.SymOcc[SO].AffOcc.Beg + A;
        R = SOAG.SymOcc[SO].RuleInd;
        if (SOAG.IsEvaluatorRule(R))
        {
            PN = GetPlanNo(R, AP);
            RS = SOAG.SymOcc[SOAG.Rule[R].SymOcc.Beg].SymInd;
            IncludeVS(RS, PN);
            for (AP1 = SOAG.Rule[R].AffOcc.Beg; AP1 <= SOAG.Rule[R].AffOcc.End; ++AP1)
            {
                AN1 = SOAG.AffOcc[AP1].AffOccNum.InRule;
                AN = SOAG.AffOcc[AP].AffOccNum.InRule;
                if (Sets.In(SOAG.Rule[R].DP[AN], AN1))
                {
                    PN1 = GetPlanNo(R, AP1);
                    if (PN < PN1)
                    {
                        IncludeVDS(RS, PN, PN1);
                    }
                }
            }
        }
        SO = SOAG.SymOcc[SO].Next;
    }
}

/**
 * SEM: Kompletiert die Initialisierung der Menge VDS (analog Step 2 der Theorie)
 */
void CompleteInitVDS()
{
    int R;
    int S;
    int SO;
    int VN1;
    int VN2;
    int V1;
    int V2;
    int RS;
    int i = ALists.firstIndex;

    while (i < VDS.Last)
    {
        S = VDS.Elem[i];
        ++i;
        VN1 = VDS.Elem[i];
        ++i;
        VN2 = VDS.Elem[i];
        ++i;
        SO = SOAG.Sym[S].FirstOcc;
        while (SO != SOAG.nil)
        {
            R = SOAG.SymOcc[SO].RuleInd;
            if (SOAG.IsEvaluatorRule(R))
            {
                if (SOAG.Rule[R].SymOcc.Beg != SO)
                {
                    V1 = SOAGVisitSeq.GetVisit(R, SO, VN1);
                    V2 = SOAGVisitSeq.GetNextVisit(V1, R, SO, VN2);
                    if (PN[V1] < PN[V2])
                    {
                        RS = SOAG.SymOcc[SOAG.Rule[SOAG.SymOcc[SO].RuleInd].SymOcc.Beg].SymInd;
                        IncludeVDS(RS, PN[V1], PN[V2]);
                    }
                }
            }
            SO = SOAG.SymOcc[SO].Next;
        }
    }
}

/**
 * IN: Symbol, Affixpos.Nr.
 * OUT: -
 * SEM: Test, ob Affixposition als Stack oder als globale Variable abgespeichert werden kann -
 *      nach Theorem 1 und 3 der Theorie
 */
void CheckStorageType(int S, int A)
{
    int R;
    int SO;
    int AP1;
    int AN1;
    int VN1;
    int AP2;
    int AN2;
    int VN2;
    int S1;
    int SO1;
    int PN1;
    int PN2;

    /**
     * IN: Symbol, Affixpos.Nr., aktuelle Regel, zwei Positionen der EVS
     */
    void CheckT2P1andT1P1(int S, int A, int R, int PN1, int PN2)
    {
        int AP3;
        int AN3;
        int AP4;
        int AN4;
        int PN3;
        int PN4;
        int SO1 = SOAG.Sym[S].FirstOcc;

        while (SO1 != SOAG.nil)
        {
            if (R == SOAG.SymOcc[SO1].RuleInd)
            {
                AP3 = SOAG.SymOcc[SO1].AffOcc.Beg + A;
                AN3 = SOAG.AffOcc[AP3].AffOccNum.InRule;
                PN3 = GetEVSPosforAffOcc(R, AP3);
                if (PN1 < PN3 && PN3 < PN2)
                {
                    disjoint = false;
                }
                for (AP4 = SOAG.Rule[R].AffOcc.Beg; AP4 <= SOAG.Rule[R].AffOcc.End;
                        ++AP4)
                {
                    AN4 = SOAG.AffOcc[AP4].AffOccNum.InRule;
                    if (Sets.In(SOAG.Rule[R].DP[AN3], AN4))
                    {
                        PN4 = GetEVSPosforAffOcc(R, AP4);
                        if (PN1 < PN3 && PN3 < PN2 && PN2 <= PN4)
                        {
                            admissible = false;
                        }
                    }
                }
            }
            SO1 = SOAG.SymOcc[SO1].Next;
        }
    }

    /**
     * IN: aktuelle Regel, zwei Positionen in der EVS
     */
    void CheckT2P2(int R, int PN1, int PN2)
    {
        int S1;
        int SO1;
        int PN;
        int VN;

        for (size_t t = ALists.firstIndex; t <= VS.Last; t += 2)
        {
            S1 = VS.Elem[t];
            VN = VS.Elem[t + 1];
            SO1 = SOAG.Sym[S1].FirstOcc;
            while (SO1 != SOAG.nil)
            {
                if (R == SOAG.SymOcc[SO1].RuleInd && SOAG.Rule[R].SymOcc.Beg != SO1)
                {
                    PN = GetEVSPosforVisit(R, SO1, VN);
                    if (PN1 < PN && PN < PN2)
                    {
                        disjoint = false;
                    }
                }
                SO1 = SOAG.SymOcc[SO1].Next;
            }
        }
    }

    /**
     * IN: aktuelle Regel, zwei Positionen in der EVS
     */
    void CheckT1P2andP3(int R, int PN1, int PN2)
    {
        int S1;
        int SO1;
        int VN3;
        int VN4;
        int PN3;
        int PN4;

        for (int t = ALists.firstIndex; t <= VDS.Last; t += 3)
        {
            S1 = VDS.Elem[t];
            VN3 = VDS.Elem[t + 1];
            VN4 = VDS.Elem[t + 2];
            SO1 = SOAG.Sym[S1].FirstOcc;
            while (SO1 != SOAG.nil)
            {
                if (R == SOAG.SymOcc[SO1].RuleInd && SOAG.Rule[R].SymOcc.Beg != SO1)
                {
                    PN3 = GetEVSPosforVisit(R, SO1, VN3);
                    PN4 = GetEVSPosforVisit(R, SO1, VN4);
                    if (PN1 < PN3 && PN3 < PN2 && PN2 < PN4 || PN3 < PN1 && PN1 < PN4 && PN4 < PN2)
                    {
                        admissible = false;
                    }
                }
                SO1 = SOAG.SymOcc[SO1].Next;
            }
        }
    }

    /**
     * IN: Affixpos.Nr., aktuelle Regel, zwei Position in der EVS
     */
    void CheckT2P3(int S, int A, int R, int PN1, int PN2)
    {
        int SO2;
        int AP1;
        int PN3;

        for (SO2 = SOAG.Rule[R].SymOcc.Beg; SO2 <= SOAG.Rule[R].SymOcc.End; ++SO2)
        {
            if (SOAG.SymOcc[SO2].SymInd == S)
            {
                AP1 = SOAG.SymOcc[SO2].AffOcc.Beg + A;
                PN3 = GetEVSPosforAffOcc(R, AP1);
                if (PN1 < PN3 && PN3 < PN2)
                {
                    disjoint = false;
                }
            }
        }
    }

    /**
     * IN: aktuelle Regel, zwei Position in der EVS
     */
    void CheckT2P4(int R, int SO, int PN1, int PN2)
    {
        int S2;
        int SO2;
        int VN3;
        int PN3;

        for (int t = ALists.firstIndex; t <= VS.Last; t += 2)
        {
            S2 = VS.Elem[t];
            VN3 = VS.Elem[t + 1];
            SO2 = SOAG.Sym[S2].FirstOcc;
            while (SO2 != SOAG.nil)
            {
                if (R == SOAG.SymOcc[SO2].RuleInd && SOAG.Rule[R].SymOcc.Beg != SO2 && SO != SO2)
                {
                    PN3 = GetEVSPosforVisit(R, SO2, VN3);
                    if (PN1 < PN3 && PN3 < PN2)
                    {
                        disjoint = false;
                    }
                }
                SO2 = SOAG.SymOcc[SO2].Next;
            }
        }
    }

    /**
     * IN: aktuelle Regel, zwei Position in der EVS
     */
    void CheckT1P4(int R, int SO, int PN1, int PN2)
    {
        int S2;
        int SO2;
        int VN3;
        int VN4;
        int PN3;
        int PN4;

        for (int t = ALists.firstIndex; t <= VDS.Last; t += 3)
        {
            S2 = VDS.Elem[t];
            VN3 = VDS.Elem[t + 1];
            VN4 = VDS.Elem[t + 2];
            SO2 = SOAG.Sym[S2].FirstOcc;
            while (SO2 != SOAG.nil)
            {
                if (R == SOAG.SymOcc[SO2].RuleInd && SOAG.Rule[R].SymOcc.Beg != SO2 && SO != SO2)
                {
                    PN3 = GetEVSPosforVisit(R, SO2, VN3);
                    PN4 = GetEVSPosforVisit(R, SO2, VN4);
                    if (PN1 < PN3 && PN3 < PN2 && PN2 < PN4)
                    {
                        admissible = false;
                    }
                }
                SO2 = SOAG.SymOcc[SO2].Next;
            }
        }
    }

    SO = SOAG.Sym[S].FirstOcc;
    while (SO != SOAG.nil)
    {
        AP1 = SOAG.SymOcc[SO].AffOcc.Beg + A;
        AN1 = SOAG.AffOcc[AP1].AffOccNum.InRule;
        R = SOAG.SymOcc[SO].RuleInd;
        if (SOAG.IsEvaluatorRule(R))
        {
            PN1 = GetEVSPosforAffOcc(R, AP1);
            for (AP2 = SOAG.Rule[R].AffOcc.Beg; AP2 <= SOAG.Rule[R].AffOcc.End; ++AP2)
            {
                AN2 = SOAG.AffOcc[AP2].AffOccNum.InRule;
                if (Sets.In(SOAG.Rule[R].DP[AN1], AN2))
                {
                    PN2 = GetEVSPosforAffOcc(R, AP2);
                    CheckT2P1andT1P1(S, A, R, PN1, PN2);
                    CheckT2P2(R, PN1, PN2);
                    CheckT1P2andP3(R, PN1, PN2);
                }
            }
        }
        SO = SOAG.SymOcc[SO].Next;
    }
    for (int t = ALists.firstIndex; t <= VDS.Last; t += 3)
    {
        S1 = VDS.Elem[t];
        VN1 = VDS.Elem[t + 1];
        VN2 = VDS.Elem[t + 2];
        SO1 = SOAG.Sym[S1].FirstOcc;
        while (SO1 != SOAG.nil)
        {
            R = SOAG.SymOcc[SO1].RuleInd;
            if (SOAG.IsEvaluatorRule(R))
            {
                if (SOAG.Rule[R].SymOcc.Beg != SO1)
                {
                    PN1 = GetEVSPosforVisit(R, SO1, VN1);
                    PN2 = GetEVSPosforVisit(R, SO1, VN2);
                    CheckT2P3(S, A, R, PN1, PN2);
                    CheckT2P4(R, SO1, PN1, PN2);
                    CheckT1P4(R, SO1, PN1, PN2);
                }
            }
            SO1 = SOAG.SymOcc[SO1].Next;
        }
    }
}

void Optimize()
{
    int S;
    int AP;
    int A;

    Init;
    GlobalVar = firstGlobalVar - 1;
    StackVar = firstStackVar - 1;
    for (S = SOAG.firstSym; S < SOAG.NextSym; ++S)
    {
        if (Sets.In(EAG.All, S))
        {
            for (AP = SOAG.Sym[S].AffPos.Beg; AP <= SOAG.Sym[S].AffPos.End; ++AP)
            {
                A = AP - SOAG.Sym[S].AffPos.Beg;
                if (!Sets.In(EAG.Pred, S) || SOAG.IsSynthesized(S, A))
                {
                    disjoint = true;
                    admissible = true;
                    InitVDSandVS(S, A);
                    CompleteInitVDS;
                    CheckStorageType(S, A);
                    if (disjoint)
                    {
                        ++GlobalVar;
                        SOAG.StorageName[AP] = -GlobalVar;
                    }
                    else if (admissible)
                    {
                        ++StackVar;
                        SOAG.StorageName[AP] = StackVar;
                    }
                }
            }
        }
    }
}

module epsilon.soag.visitseq;

import EAG = epsilon.eag;
import runtime;
import hash = epsilon.soag.hash;
import SOAG = epsilon.soag.soag;
import std.range;

const noVisit = -1;
int[] InDeg;

/**
 * IN:  -
 * OUT: -
 * SEM: Berechnung der maximalen Visits in Sym[X].MaxPart
 *      und der Visit-Nummer der Affixpositionen in PartNum[AffPos].
 */
void ComputeVisitNo()
{
    import std.conv : to;
    import std.exception : enforce;
    import std.format: format;

    int AP;
    int MaxPart;
    int PartNum;

    foreach (S; EAG.All.bitsSet)
        if (!EAG.Pred[S])
        {
            MaxPart = DIV(SOAG.Sym[S].MaxPart + 1, 2).to!int;
            SOAG.Sym[S].MaxPart = MaxPart;
            for (AP = SOAG.Sym[S].AffPos.Beg; AP <= SOAG.Sym[S].AffPos.End; ++AP)
            {
                enforce(SOAG.PartNum[AP] >= 0,
                        format!"partition number for affix position %d at symbol %s not determined"
                            (AP, EAG.HNontRepr(S)));

                PartNum = DIV(SOAG.PartNum[AP] + 1, 2).to!int;
                SOAG.PartNum[AP] = MaxPart - PartNum + 1;
            }
        }
}

/**
 * IN:  Affixparameter
 * OUT: Visit-Nummer des Affixparameters
 * SEM: Auslesen der Visit-Nummer des Affixparameters, Schnittstellenprozedur
 */
int GetVisitNo(int AP) @nogc nothrow @safe
{
    const S = SOAG.SymOcc[SOAG.AffOcc[AP].SymOccInd].SymInd;

    return SOAG.PartNum[SOAG.Sym[S].AffPos.Beg + SOAG.AffOcc[AP].AffOccNum.InSym];
}

/**
 * IN:  Symbolvorkommen, die keine Prädikate sind
 * OUT: die maximale Visit-Nummer dieses Symbols
 * SEM: Auslesen der maximalen Visit-Nummer des Symbolvorkommens, Schnittstellenprozedur
 */
int GetMaxVisitNo(int SO) @nogc nothrow @safe
{
    return SOAG.Sym[SOAG.SymOcc[SO].SymInd].MaxPart;
}

/**
 * IN:  aktueller Visit, Regel, aktuller Visit, Symbolvorkommen, Visitnummer
 * OUT: Nummer des Eintrages in der Visitsequenz der Regel
 * SEM: Durchsucht die Visitsequenz nach dem Visit des Symbolvorkommens mit entsprechender Besuchsnummer.
 */
int GetNextVisit(int V, int R, int SO, int VN) @nogc nothrow @safe
{
    while (V <= SOAG.Rule[R].VS.End)
    {
        if (auto visit = cast(SOAG.Visit) SOAG.VS[V])
        {
            if (visit.SymOcc == SO && visit.VisitNo == VN)
                return V;
        }
        else if (auto call = cast(SOAG.Call) SOAG.VS[V])
        {
            if (call.SymOcc == SO)
                return V;
        }
        else if (auto leave = cast(SOAG.Leave) SOAG.VS[V])
        {
            if (leave.VisitNo == VN && SOAG.Rule[R].SymOcc.Beg == SO)
                return V;
        }
        ++V;
    }
    return noVisit;
}

/**
 * IN:  Regel, Symbolvorkommen, Visitnummer
 * OUT: Nummer des Eintrages in der Visitsequenz der Regel
 * SEM: Durchsucht die Visitsequenz nach dem Visit des Symbolvorkommens mit entsprechender Besuchsnummer.
 */
int GetVisit(int R, int SO, int VN) @nogc nothrow @safe
{
    return GetNextVisit(SOAG.Rule[R].VS.Beg, R, SO, VN);
}

/**
 * IN:  Affixparameter
 * OUT: Instruktion oder NIL für NOP
 * SEM: Erzeugung einer Instruktion in Abhäengigkeit vom übergebenen Affixparameter
 */
SOAG.Instruction MapVS(int AO) nothrow
{
    if (!EAG.ParamBuf[SOAG.AffOcc[AO].ParamBufInd].isDef)
        return null;

    const SO = SOAG.AffOcc[AO].SymOccInd;

    if (SOAG.IsPredNont(SO))
    {
        SOAG.Call Call = new SOAG.Call;

        Call.SymOcc = SO;
        return Call;
    }

    const R = SOAG.SymOcc[SO].RuleInd;

    if (SOAG.Rule[R].SymOcc.Beg == SO)
    {
        if (GetVisitNo(AO) - 1 > 0)
        {
            SOAG.Leave Leave = new SOAG.Leave;

            Leave.VisitNo = GetVisitNo(AO) - 1;
            return Leave;
        }
        return null;
    }
    else
    {
        SOAG.Visit Visit = new SOAG.Visit;

        Visit.SymOcc = SO;
        Visit.VisitNo = GetVisitNo(AO);
        return Visit;
    }
}

/**
 * IN:  Symbolvorkommen
 * OUT: Instruktion
 * SEM: Berechnung der abschliessenden Instruktionen für ein Symbolvorkommen
 */
SOAG.Instruction CompleteTraversal(int SO) nothrow
{
    if (SOAG.IsPredNont(SO))
    {
        SOAG.Call Call = new SOAG.Call;

        Call.SymOcc = SO;
        return Call;
    }

    const R = SOAG.SymOcc[SO].RuleInd;

    if (SOAG.Rule[R].SymOcc.Beg == SO)
    {
        SOAG.Leave Leave = new SOAG.Leave;

        Leave.VisitNo = GetMaxVisitNo(SO);
        return Leave;
    }

    SOAG.Visit Visit = new SOAG.Visit;

    Visit.SymOcc = SO;
    Visit.VisitNo = GetMaxVisitNo(SO);
    return Visit;
}

/**
 * IN:  Regel
 * OUT: -
 * SEM: topologische Sortierung der Affixparameter anhand ihrer Abhängigkeiten
 */
void TopSort(int R)
{
    int AO;
    int AN;
    int BO;
    int BN;
    SOAG.Instruction Instr;
    int[] ZeroInDeg;

    for (BO = SOAG.Rule[R].AffOcc.End; BO >= SOAG.Rule[R].AffOcc.Beg; --BO)
    {
        BN = SOAG.AffOcc[BO].AffOccNum.InRule;
        InDeg[BN] = 0;
        for (AO = SOAG.Rule[R].AffOcc.Beg; AO <= SOAG.Rule[R].AffOcc.End; ++AO)
        {
            AN = SOAG.AffOcc[AO].AffOccNum.InRule;
            if (SOAG.Rule[R].TDP[AN][BN])
                ++InDeg[BN];
        }
        if (InDeg[BN] == 0)
            ZeroInDeg ~= BO;
    }
    while (!ZeroInDeg.empty)
    {
        AO = ZeroInDeg.back;
        ZeroInDeg.popBack;
        Instr = MapVS(AO);
        AN = SOAG.AffOcc[AO].AffOccNum.InRule;
        if (!hash.IsIn(Instr))
        {
            hash.Enter(Instr);
            SOAG.AppVS(Instr);
        }
        for (BO = SOAG.Rule[R].AffOcc.End; BO >= SOAG.Rule[R].AffOcc.Beg; --BO)
        {
            BN = SOAG.AffOcc[BO].AffOccNum.InRule;
            if (SOAG.Rule[R].TDP[AN][BN])
            {
                --InDeg[BN];
                if (InDeg[BN] == 0)
                    ZeroInDeg ~= BO;
            }
        }
    }
}

/**
 * SEM: Generierung der Visit-Sequenzen
 */
void Generate()
{
    int SO;
    SOAG.Instruction Instr;

    ComputeVisitNo;
    // hash.Init(SOAG.MaxAffNumInRule); // does not work if (MaxAffNumInRule == 0)
    hash.Init(SOAG.MaxAffNumInRule + 1);
    InDeg = new int[SOAG.MaxAffNumInRule + 1];
    for (int R = SOAG.firstRule; R < SOAG.NextRule; ++R)
    {
        SOAG.Rule[R].VS.Beg = SOAG.NextVS;
        if (SOAG.IsEvaluatorRule(R))
        {
            hash.Reset;
            TopSort(R);
            for (SO = SOAG.Rule[R].SymOcc.Beg + 1; SO <= SOAG.Rule[R].SymOcc.End; ++SO)
            {
                Instr = CompleteTraversal(SO);
                if (!hash.IsIn(Instr))
                    SOAG.AppVS(Instr);
            }
            Instr = CompleteTraversal(SOAG.Rule[R].SymOcc.Beg);
            if (!hash.IsIn(Instr))
                SOAG.AppVS(Instr);
        }
        SOAG.Rule[R].VS.End = SOAG.NextVS - 1;
    }
}

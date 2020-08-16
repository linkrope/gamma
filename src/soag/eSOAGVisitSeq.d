module soag.eSOAGVisitSeq;

import runtime;
import EAG = eEAG;
import SOAG = soag.eSOAG;
import HashTab = soag.eSOAGHash;
import Sets = eSets;
import Stacks = soag.eStacks;
import IO = eIO;
import Protocol = soag.eSOAGProtocol;

const noVisit = -1;
SOAG.OpenInteger InDeg;
Stacks.Stack ZeroInDeg;

/**
 * IN:  -
 * OUT: -
 * SEM: Berechnung der maximalen Visits in Sym[X].MaxPart
 *      und der Visit-Nummer der Affixpositionen in PartNum[AffPos].
 */
void ComputeVisitNo()
{
    import std.conv : to;
    int S;
    int AP;
    int MaxPart;
    int PartNum;
    for (S = SOAG.firstSym; S <= SOAG.NextSym - 1; ++S)
    {
        MaxPart = DIV(SOAG.Sym[S].MaxPart + 1, 2).to!int;
        SOAG.Sym[S].MaxPart = MaxPart;
        for (AP = SOAG.Sym[S].AffPos.Beg; AP <= SOAG.Sym[S].AffPos.End; ++AP)
        {
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
int GetVisitNo(int AP)
{
    int S;
    S = SOAG.SymOcc[SOAG.AffOcc[AP].SymOccInd].SymInd;
    return SOAG.PartNum[SOAG.Sym[S].AffPos.Beg + SOAG.AffOcc[AP].AffOccNum.InSym];
}

/**
 * IN:  Symbolvorkommen, die keine Prädikate sind
 * OUT: die maximale Visit-Nummer dieses Symbols
 * SEM: Auslesen der maximalen Visit-Nummer des Symbolvorkommens, Schnittstellenprozedur
 */
int GetMaxVisitNo(int SO)
{
    return SOAG.Sym[SOAG.SymOcc[SO].SymInd].MaxPart;
}

/**
 * IN:  aktueller Visit, Regel, aktuller Visit, Symbolvorkommen, Visitnummer
 * OUT: Nummer des Eintrages in der Visitsequenz der Regel
 * SEM: Durchsucht die Visitsequenz nach dem Visit des Symbolvorkommens mit entsprechender Besuchsnummer.
 */
int GetNextVisit(int V, int R, int SO, int VN)
{
    while (V <= SOAG.Rule[R].VS.End)
    {
        if (cast(SOAG.Visit) SOAG.VS[V] !is null)
        {
            if ((cast(SOAG.Visit) SOAG.VS[V]).SymOcc == SO && (cast(SOAG.Visit) SOAG.VS[V]).VisitNo == VN)
            {
                return V;
            }
        }
        else if (cast(SOAG.Call) SOAG.VS[V] !is null)
        {
            if ((cast(SOAG.Call) SOAG.VS[V]).SymOcc == SO)
            {
                return V;
            }
        }
        else if (cast(SOAG.Leave) SOAG.VS[V] !is null)
        {
            if ((cast(SOAG.Leave) SOAG.VS[V]).VisitNo == VN && SOAG.Rule[R].SymOcc.Beg == SO)
            {
                return V;
            }
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
int GetVisit(int R, int SO, int VN)
{
    return GetNextVisit(SOAG.Rule[R].VS.Beg, R, SO, VN);
}

/**
 * IN:  Affixparameter
 * OUT: Instruktion oder NIL für NOP
 * SEM: Erzeugung einer Instruktion in Abhäengigkeit vom übergebenen Affixparameter
 */
SOAG.Instruction MapVS(int AO)
{
    SOAG.Visit Visit;
    SOAG.Leave Leave;
    SOAG.Call Call;
    int SO;
    int R;
    if (EAG.ParamBuf[SOAG.AffOcc[AO].ParamBufInd].isDef)
    {
        SO = SOAG.AffOcc[AO].SymOccInd;
        if (SOAG.IsPredNont(SO))
        {
            NEW(Call);
            Call.SymOcc = SO;
            return Call;
        }
        else
        {
            R = SOAG.SymOcc[SO].RuleInd;
            if (SOAG.Rule[R].SymOcc.Beg == SO)
            {
                if (GetVisitNo(AO) - 1 > 0)
                {
                    NEW(Leave);
                    Leave.VisitNo = GetVisitNo(AO) - 1;
                    return Leave;
                }
                else
                {
                    return null;
                }
            }
            else
            {
                NEW(Visit);
                Visit.SymOcc = SO;
                Visit.VisitNo = GetVisitNo(AO);
                return Visit;
            }
        }
    }
    else
    {
        return null;
    }
}

/**
 * IN:  Symbolvorkommen
 * OUT: Instruktion
 * SEM: Berechnung der abschliessenden Instruktionen für ein Symbolvorkommen
 */
SOAG.Instruction CompleteTraversal(int SO)
{
    SOAG.Visit Visit;
    SOAG.Leave Leave;
    SOAG.Call Call;
    int R;
    int MaxVisitNo;
    if (SOAG.IsPredNont(SO))
    {
        NEW(Call);
        Call.SymOcc = SO;
        return Call;
    }
    else
    {
        R = SOAG.SymOcc[SO].RuleInd;
        if (SOAG.Rule[R].SymOcc.Beg == SO)
        {
            NEW(Leave);
            Leave.VisitNo = GetMaxVisitNo(SO);
            return Leave;
        }
        else
        {
            NEW(Visit);
            Visit.SymOcc = SO;
            Visit.VisitNo = GetMaxVisitNo(SO);
            return Visit;
        }
    }
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
    Stacks.Reset(ZeroInDeg);
    for (BO = SOAG.Rule[R].AffOcc.End; BO >= SOAG.Rule[R].AffOcc.Beg; --BO)
    {
        BN = SOAG.AffOcc[BO].AffOccNum.InRule;
        InDeg[BN] = 0;
        for (AO = SOAG.Rule[R].AffOcc.Beg; AO <= SOAG.Rule[R].AffOcc.End; ++AO)
        {
            AN = SOAG.AffOcc[AO].AffOccNum.InRule;
            if (Sets.In(SOAG.Rule[R].TDP[AN], BN))
            {
                ++InDeg[BN];
            }
        }
        if (InDeg[BN] == 0)
        {
            Stacks.Push(ZeroInDeg, BO);
        }
    }
    while (!Stacks.IsEmpty(ZeroInDeg))
    {
        Stacks.Pop(ZeroInDeg, AO);
        Instr = MapVS(AO);
        AN = SOAG.AffOcc[AO].AffOccNum.InRule;
        if (!HashTab.IsIn(Instr))
        {
            HashTab.Enter(Instr);
            SOAG.AppVS(Instr);
        }
        for (BO = SOAG.Rule[R].AffOcc.End; BO >= SOAG.Rule[R].AffOcc.Beg; --BO)
        {
            BN = SOAG.AffOcc[BO].AffOccNum.InRule;
            if (Sets.In(SOAG.Rule[R].TDP[AN], BN))
            {
                --InDeg[BN];
                if (InDeg[BN] == 0)
                {
                    Stacks.Push(ZeroInDeg, BO);
                }
            }
        }
    }
}

/**
 * SEM: Generierung der Visit-Sequenzen
 */
void Generate()
{
    int R;
    int SO;
    int MaxTry;
    int S;
    int V;
    SOAG.Instruction Instr;
    MaxTry = 0;
    ComputeVisitNo;
    HashTab.Init(SOAG.MaxAffNumInRule);
    Stacks.New(ZeroInDeg, 32);
    NEW(InDeg, SOAG.MaxAffNumInRule + 1);
    for (R = SOAG.firstRule; R <= SOAG.NextRule - 1; ++R)
    {
        SOAG.Rule[R].VS.Beg = SOAG.NextVS;
        if (SOAG.IsEvaluatorRule(R))
        {
            HashTab.Reset;
            TopSort(R);
            if (MaxTry < HashTab.MaxTry)
            {
                MaxTry = HashTab.MaxTry;
            }
            for (SO = SOAG.Rule[R].SymOcc.Beg + 1; SO <= SOAG.Rule[R].SymOcc.End;
                    ++SO)
            {
                Instr = CompleteTraversal(SO);
                if (!HashTab.IsIn(Instr))
                {
                    SOAG.AppVS(Instr);
                }
            }
            Instr = CompleteTraversal(SOAG.Rule[R].SymOcc.Beg);
            if (!HashTab.IsIn(Instr))
            {
                SOAG.AppVS(Instr);
            }
        }
        SOAG.Rule[R].VS.End = SOAG.NextVS - 1;
    }
}
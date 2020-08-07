module soag.eSOAG;

import runtime;
import EAG = eEAG;
import IO = eIO;
import Sets = eSets;
import Predicates = ePredicates;

const firstSym = EAG.firstHNont;
const firstRule = 0;
const firstSymOcc = 0;
const firstAffOcc = 0;
const firstPartNum = 0;
const firstAffOccNum = 0;
const firstVS = 1;
const firstDefAffOcc = EAG.firstVar;
const firstStorageName = 0;
const firstAffixApplCnt = EAG.firstVar;
const nil = -1;

struct SymDesc
{
    int FirstOcc;
    int MaxPart;
    EAG.ScopeDesc AffPos;
}

alias OpenTDP = Sets.OpenSet[];

class RuleDesc
{
    EAG.ScopeDesc SymOcc;
    EAG.ScopeDesc AffOcc;
    OpenTDP TDP;
    OpenTDP DP;
    EAG.ScopeDesc VS;
}

alias RuleBase = RuleDesc;

class EmptyRule : RuleDesc
{
    EAG.Rule Rule;
}

class OrdRule : RuleDesc
{
    EAG.Alt Alt;
}

struct SymOccDesc
{
    int SymInd;
    int RuleInd;
    EAG.Nont Nont;
    EAG.ScopeDesc AffOcc;
    int Next;
}

struct AffOccNumRecord
{
    int InRule;
    int InSym;
}

struct AffOccDesc
{
    int ParamBufInd;
    int SymOccInd;
    AffOccNumRecord AffOccNum;
}

class InstructionDesc
{
}

alias Instruction = InstructionDesc;

class Visit : InstructionDesc
{
    int SymOcc;
    int VisitNo;
}

class Leave : InstructionDesc
{
    int VisitNo;
}

class Call : InstructionDesc
{
    int SymOcc;
}

alias OpenInteger = int[];
alias OpenSym = SymDesc[];
alias OpenPartNum = OpenInteger;
alias OpenRule = RuleBase[];
alias OpenSymOcc = SymOccDesc[];
alias OpenAffOcc = AffOccDesc[];
alias OpenVS = Instruction[];
alias OpenDefAffOcc = OpenInteger;
alias OpenStorageName = OpenInteger;
alias OpenAffixApplCnt = OpenInteger;
OpenSym Sym;
OpenPartNum PartNum;
OpenRule Rule;
OpenSymOcc SymOcc;
OpenAffOcc AffOcc;
OpenVS VS;
OpenDefAffOcc DefAffOcc;
OpenStorageName StorageName;
OpenAffixApplCnt AffixApplCnt;
int NextSym;
int NextPartNum;
int NextRule;
int NextSymOcc;
int NextAffOcc;
int NextVS;
int NextDefAffOcc;
int NextStorageName;
int NextAffixApplCnt;
int MaxAffNumInRule;
int MaxAffNumInSym;
int MaxPart;
const abnormalyError = 1;
const cyclicTDP = 2;
const notLeftDefined = 3;
const notEnoughMemory = 99;

void Error(T)(int ErrorType, T Proc)
{
    IO.WriteString(IO.Msg, "ERROR: ");
    switch (ErrorType)
    {
    case abnormalyError:
        IO.WriteText(IO.Msg, "abnormaly error ");
        break;
    case notEnoughMemory:
        IO.WriteText(IO.Msg, "memory allocation failed ");
        break;
    case cyclicTDP:
        IO.WriteText(IO.Msg, "TDP is cyclic...aborted\n");
        break;
    case notLeftDefined:
        IO.WriteText(IO.Msg, "Grammar are not left defined\n");
        break;
    default:
        assert(0);
    }
    if (ErrorType == abnormalyError || ErrorType == notEnoughMemory)
    {
        IO.WriteString(IO.Msg, "in procedure ");
        IO.WriteString(IO.Msg, Proc);
        IO.WriteLn(IO.Msg);
    }
    IO.Update(IO.Msg);
    throw new Exception("TODO");
}

void Expand()
{
    OpenRule Rule1;
    OpenSymOcc SymOcc1;
    OpenAffOcc AffOcc1;
    OpenVS VS1;
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

    if (NextAffOcc >= AffOcc.length)
    {
        NEW(AffOcc1, NewLen(AffOcc.length));
        for (i = firstAffOcc; i <= AffOcc.length - 1; ++i)
        {
            AffOcc1[i] = AffOcc[i];
        }
        AffOcc = AffOcc1;
    }
    if (NextSymOcc >= SymOcc.length)
    {
        NEW(SymOcc1, NewLen(SymOcc.length));
        for (i = firstSymOcc; i <= SymOcc.length - 1; ++i)
        {
            SymOcc1[i] = SymOcc[i];
        }
        SymOcc = SymOcc1;
    }
    if (NextRule >= Rule.length)
    {
        NEW(Rule1, NewLen(Rule.length));
        for (i = firstRule; i <= Rule.length - 1; ++i)
        {
            Rule1[i] = Rule[i];
        }
        Rule = Rule1;
    }
    if (NextVS >= VS.length)
    {
        NEW(VS1, NewLen(VS.length));
        for (i = firstVS; i <= VS.length - 1; ++i)
        {
            VS1[i] = VS[i];
        }
        VS = VS1;
    }
}

void AppAffOcc(int Params)
{
    if (Params != EAG.empty)
    {
        while (EAG.ParamBuf[Params].Affixform != EAG.nil)
        {
            AffOcc[NextAffOcc].ParamBufInd = Params;
            AffOcc[NextAffOcc].SymOccInd = NextSymOcc;
            AffOcc[NextAffOcc].AffOccNum.InRule = NextAffOcc - Rule[NextRule].AffOcc.Beg;
            AffOcc[NextAffOcc].AffOccNum.InSym = NextAffOcc - SymOcc[NextSymOcc].AffOcc.Beg;
            ++NextAffOcc;
            if (NextAffOcc >= AffOcc.length)
            {
                Expand;
            }
            ++Params;
        }
    }
}

void AppSymOccs(EAG.Factor Factor)
{
    while (Factor !is null)
    {
        if (cast(EAG.Nont) Factor !is null)
        {
            SymOcc[NextSymOcc].SymInd = (cast(EAG.Nont) Factor).Sym;
            SymOcc[NextSymOcc].RuleInd = NextRule;
            SymOcc[NextSymOcc].Nont = cast(EAG.Nont) Factor;
            SymOcc[NextSymOcc].AffOcc.Beg = NextAffOcc;
            AppAffOcc((cast(EAG.Nont) Factor).Actual.Params);
            SymOcc[NextSymOcc].AffOcc.End = NextAffOcc - 1;
            SymOcc[NextSymOcc].Next = Sym[(cast(EAG.Nont) Factor).Sym].FirstOcc;
            Sym[(cast(EAG.Nont) Factor).Sym].FirstOcc = NextSymOcc;
            ++NextSymOcc;
            if (NextSymOcc >= SymOcc.length)
            {
                Expand;
            }
        }
        Factor = Factor.Next;
    }
}

void AppLeftSymOcc(int leftSym, int Params)
{
    SymOcc[NextSymOcc].SymInd = leftSym;
    SymOcc[NextSymOcc].RuleInd = NextRule;
    SymOcc[NextSymOcc].Nont = null;
    SymOcc[NextSymOcc].AffOcc.Beg = NextAffOcc;
    AppAffOcc(Params);
    SymOcc[NextSymOcc].AffOcc.End = NextAffOcc - 1;
    SymOcc[NextSymOcc].Next = Sym[leftSym].FirstOcc;
    Sym[leftSym].FirstOcc = NextSymOcc;
    ++NextSymOcc;
    if (NextSymOcc >= SymOcc.length)
    {
        Expand;
    }
}

void AppEmptyRule(int leftSym, EAG.Rule EAGRule)
{
    EmptyRule A;
    NEW(A);
    Rule[NextRule] = A;
    A.Rule = EAGRule;
    A.SymOcc.Beg = NextSymOcc;
    A.AffOcc.Beg = NextAffOcc;
    if (cast(EAG.Opt) EAGRule !is null)
    {
        AppLeftSymOcc(leftSym, (cast(EAG.Opt) EAGRule).Formal.Params);
    }
    else if (cast(EAG.Rep) EAGRule !is null)
    {
        AppLeftSymOcc(leftSym, (cast(EAG.Rep) EAGRule).Formal.Params);
    }
    A.SymOcc.End = NextSymOcc - 1;
    A.AffOcc.End = NextAffOcc - 1;
    ++NextRule;
    if (NextRule >= Rule.length)
    {
        Expand;
    }
}

void AppRule(EAG.Alt EAGAlt)
{
    OrdRule A;
    NEW(A);
    Rule[NextRule] = A;
    A.Alt = EAGAlt;
    A.SymOcc.Beg = NextSymOcc;
    A.AffOcc.Beg = NextAffOcc;
    AppLeftSymOcc(EAGAlt.Up, EAGAlt.Formal.Params);
    AppSymOccs(EAGAlt.Sub);
    A.SymOcc.End = NextSymOcc - 1;
    A.AffOcc.End = NextAffOcc - 1;
    ++NextRule;
    if (NextRule >= Rule.length)
    {
        Expand;
    }
}

void AppRepRule(EAG.Alt EAGAlt)
{
    OrdRule A;
    NEW(A);
    Rule[NextRule] = A;
    A.Alt = EAGAlt;
    A.SymOcc.Beg = NextSymOcc;
    A.AffOcc.Beg = NextAffOcc;
    AppLeftSymOcc(EAGAlt.Up, EAGAlt.Formal.Params);
    AppSymOccs(EAGAlt.Sub);
    AppLeftSymOcc(EAGAlt.Up, EAGAlt.Actual.Params);
    A.SymOcc.End = NextSymOcc - 1;
    A.AffOcc.End = NextAffOcc - 1;
    ++NextRule;
    if (NextRule >= Rule.length)
    {
        Expand;
    }
}
/**
 * IN:  Instruktion
 * OUT: -
 * SEM: fügt eine Instruktion in die Datenstruktur VS ein
 */
void AppVS(ref Instruction I)
{
    VS[NextVS] = I;
    ++NextVS;
    if (NextVS >= VS.length)
    {
        Expand;
    }
}

/**
 * IN:  Symbol, Nummer des Affixposition
 * OUT: boolscher Wert
 * SEM: Test, ob Affixposition inherited ist
 */
bool IsInherited(int S, int AffOccNum)
{
    return EAG.DomBuf[EAG.HNont[S].Sig + AffOccNum] < 0;
}

/**
 * IN:  Symbol, Nummer des Affixposition
 * OUT: boolscher Wert
 * SEM: Test, ob Affixposition synthesized ist
 */
bool IsSynthesized(int S, int AffOccNum)
{
    return EAG.DomBuf[EAG.HNont[S].Sig + AffOccNum] > 0;
}

/**
 * IN:  Symbol, Nummern zweier Affixpositionen zum Symbol
 * OUT: boolscher Wert
 * SEM: Test, ob die beiden Affixpositionen orientierbar sind
 */
bool IsOrientable(int S, int AffOccNum1, int AffOccNum2)
{
    return IsInherited(S, AffOccNum1) && IsSynthesized(S, AffOccNum2)
        || IsInherited(S, AffOccNum2) && IsSynthesized(S, AffOccNum1);
}

/**
 * IN:  Regel
 * OUT: boolscher Wert
 * SEM: Test, ob eine Evaluatorregel vorliegt
 * PRECOND: Predicates.Check muss vorher ausgewertet sein
 */
bool IsEvaluatorRule(int R)
{
    return !Sets.In(EAG.Pred, SymOcc[Rule[R].SymOcc.Beg].SymInd);
}

/**
 * IN:  Symbolvorkommen
 * OUT: boolscher Wert
 * SEM: Test, ob ein Prädikat vorliegt
 * PRECOND: Predicates.Check muss vorher ausgewertet sein
 */
bool IsPredNont(int SO)
{
    return Sets.In(EAG.Pred, SymOcc[SO].SymInd);
}

/**
 * IN:  zwei Instruktionen aus der Visit-Sequenz
 * OUT: boolscher Wert
 * SEM: Test, ob zwei Instruktionnen gleich sind;
 *      etwas optimiert für den Fall, dass einer oder beide Parameter nil ist
 */
bool isEqual(Instruction I1, Instruction I2)
{
    if (I1 is null && I2 is null)
    {
        return true;
    }
    else if (I1 is null || I2 is null)
    {
        return false;
    }
    else if (cast(Visit) I1 !is null && cast(Visit) I2 !is null)
    {
        return (cast(Visit) I1).SymOcc == (cast(Visit) I2).SymOcc
            && (cast(Visit) I1).VisitNo == (cast(Visit) I2).VisitNo;
    }
    else if (cast(Leave) I1 !is null && cast(Leave) I2 !is null)
    {
        return (cast(Leave) I1).VisitNo == (cast(Leave) I2).VisitNo;
    }
    else if (cast(Call) I1 !is null && cast(Call) I2 !is null)
    {
        return (cast(Call) I1).SymOcc == (cast(Call) I2).SymOcc;
    }
    else
    {
        return false;
    }
}

/**
 * SEM: Initialisierung der SOAG-Datenstruktur; Transformation der EAG-Datenstruktur
 */
void Init()
{
    EAG.Alt A;
    int i;
    int a;
    int Max;
    NEW(Sym, EAG.NextHNont);
    NEW(Rule, 128);
    NEW(SymOcc, 256);
    NEW(AffOcc, 512);
    NEW(VS, 512);
    NEW(DefAffOcc, EAG.NextVar);
    NEW(AffixApplCnt, EAG.NextVar);
    StorageName = null;
    NextSym = EAG.NextHNont;
    NextRule = firstRule;
    NextSymOcc = firstSymOcc;
    NextAffOcc = firstAffOcc;
    NextVS = firstVS;
    NextDefAffOcc = EAG.NextVar;
    NextStorageName = nil;
    NextAffixApplCnt = EAG.NextVar;
    Predicates.Check;
    for (i = EAG.firstHNont; i <= EAG.NextHNont - 1; ++i)
    {
        Sym[i].FirstOcc = nil;
    }
    for (i = EAG.firstHNont; i <= EAG.NextHNont - 1; ++i)
    {
        if (Sets.In(EAG.All, i))
        {
            if (cast(EAG.Rep) EAG.HNont[i].Def !is null)
            {
                A = EAG.HNont[i].Def.Sub;
                while (A !is null)
                {
                    AppRepRule(A);
                    A = A.Next;
                }
            }
            else
            {
                A = EAG.HNont[i].Def.Sub;
                while (A !is null)
                {
                    AppRule(A);
                    A = A.Next;
                }
            }
            if (cast(EAG.Rep) EAG.HNont[i].Def !is null || cast(EAG.Opt) EAG.HNont[i].Def !is null)
            {
                AppEmptyRule(i, EAG.HNont[i].Def);
            }
        }
    }
    MaxAffNumInRule = 0;
    for (i = firstRule; i <= NextRule - 1; ++i)
    {
        Max = Rule[i].AffOcc.End - Rule[i].AffOcc.Beg;
        if (Max > MaxAffNumInRule)
        {
            MaxAffNumInRule = Max;
        }
        if (IsEvaluatorRule(i) && Max >= 0)
        {
            NEW(Rule[i].TDP, Max + 1);
            NEW(Rule[i].DP, Max + 1);
            for (a = firstAffOccNum; a <= Max; ++a)
            {
                Sets.New(Rule[i].TDP[a], Max + 1);
                Sets.New(Rule[i].DP[a], Max + 1);
            }
        }
    }
    MaxAffNumInSym = 0;
    NextPartNum = firstPartNum;
    for (i = EAG.firstHNont; i <= EAG.NextHNont - 1; ++i)
    {
        if (Sets.In(EAG.All, i))
        {
            Max = SymOcc[Sym[i].FirstOcc].AffOcc.End - SymOcc[Sym[i].FirstOcc].AffOcc.Beg;
            Sym[i].AffPos.Beg = NextPartNum;
            NextPartNum = NextPartNum + Max;
            Sym[i].AffPos.End = NextPartNum;
            ++NextPartNum;
            if (Max > MaxAffNumInSym)
            {
                MaxAffNumInSym = Max;
            }
            Sym[i].MaxPart = 0;
        }
    }
    NEW(PartNum, NextPartNum);
    MaxPart = 0;
    for (i = EAG.firstVar; i <= EAG.NextVar - 1; ++i)
    {
        DefAffOcc[i] = -1;
        AffixApplCnt[i] = 0;
    }
}

static this()
{
    IO.WriteText(IO.Msg, "SOAG-Evaluatorgenerator 1.06 dk 14.03.98\n");
    IO.Update(IO.Msg);
}

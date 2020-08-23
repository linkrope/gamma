module soag.eSOAGProtocol;

import runtime;
import SOAG = soag.eSOAG;
import EAG = eEAG;
import IO = eIO;
import Scanner = eScanner;
import Sets = eSets;

const standardLevel = 1;
const outRuleData = 2;
const outSymOccData = 3;
const outAffOccData = 4;
int Level;
IO.TextOut Out;

void WriteAffixVariables(int i)
{
    int MA;
    if (i < 0)
    {
        if (EAG.Var[-i].Num < 0)
        {
            IO.WriteString(Out, "#");
        }
        EAG.WriteVar(Out, -i);
        IO.WriteInt(Out, EAG.Var[-i].Num);
    }
    else
    {
        for (MA = 1; MA <= EAG.MAlt[EAG.NodeBuf[i]].Arity; ++MA)
        {
            WriteAffixVariables(EAG.NodeBuf[i + MA]);
        }
    }
}

void WriteAffix(int i)
{
    int a;
    int m;
    if (i < 0)
    {
        if (EAG.Var[-i].Num < 0)
        {
            IO.WriteString(Out, "#");
        }
        EAG.WriteVar(Out, -i);
        IO.WriteString(Out, "(");
        IO.WriteInt(Out, EAG.Var[-i].Num);
        IO.WriteString(Out, ") ");
    }
    else
    {
        a = 0;
        m = EAG.MAlt[EAG.NodeBuf[i]].Right;
        while (EAG.MembBuf[m] != EAG.nil)
        {
            if (EAG.MembBuf[m] < 0)
            {
                Scanner.WriteRepr(Out, EAG.MTerm[-EAG.MembBuf[m]].Id);
                IO.WriteString(Out, " ");
            }
            else
            {
                ++a;
                WriteAffix(EAG.NodeBuf[i + a]);
            }
            ++m;
        }
    }
}

void WriteAffOcc(int a)
{
    int p;
    p = SOAG.AffOcc[a].ParamBufInd;
    if (EAG.ParamBuf[p].isDef)
    {
        IO.WriteString(Out, "-");
    }
    else
    {
        IO.WriteString(Out, "+");
    }
    if (EAG.ParamBuf[p].Affixform < 0)
    {
        EAG.WriteVar(Out, -EAG.ParamBuf[p].Affixform);
        IO.WriteString(Out, "(");
        IO.WriteInt(Out, EAG.Var[-EAG.ParamBuf[p].Affixform].Num);
        IO.WriteString(Out, ") ");
    }
    else
    {
        WriteAffix(EAG.ParamBuf[p].Affixform);
    }
    if (EAG.ParamBuf[p + 1].Affixform != EAG.nil)
    {
        IO.WriteString(Out, ", ");
    }
}

void WriteSymOcc(int s)
{
    int i;
    EAG.WriteHNont(Out, SOAG.SymOcc[s].SymInd);
    IO.WriteString(Out, "< ");
    for (i = SOAG.SymOcc[s].AffOcc.Beg; i <= SOAG.SymOcc[s].AffOcc.End; ++i)
    {
        WriteAffOcc(i);
    }
    IO.WriteString(Out, " >");
    IO.Update(Out);
}

void WriteAffOccData(int s)
{
    IO.WriteString(Out, "AffOcc[");
    IO.WriteInt(Out, s);
    IO.WriteText(Out, "]: ");
    WriteAffOcc(s);
    IO.WriteLn(Out);
    IO.WriteString(Out, "  Variables: ");
    WriteAffixVariables(EAG.ParamBuf[SOAG.AffOcc[s].ParamBufInd].Affixform);
    IO.WriteLn(Out);
    IO.WriteString(Out, "         ParamBufInd: ");
    IO.WriteInt(Out, SOAG.AffOcc[s].ParamBufInd);
    IO.WriteLn(Out);
    IO.WriteString(Out, "           SymOccInd: ");
    IO.WriteInt(Out, SOAG.AffOcc[s].SymOccInd);
    IO.WriteLn(Out);
    IO.WriteString(Out, "    AffOccNum.InRule: ");
    IO.WriteInt(Out, SOAG.AffOcc[s].AffOccNum.InRule);
    IO.WriteLn(Out);
    IO.WriteString(Out, "     AffOccNum.InSym: ");
    IO.WriteInt(Out, SOAG.AffOcc[s].AffOccNum.InSym);
    IO.WriteLn(Out);
}

void WriteSymOccData(int s)
{
    IO.WriteString(Out, "SymOcc[");
    IO.WriteInt(Out, s);
    IO.WriteText(Out, "]: ");
    WriteSymOcc(s);
    IO.WriteLn(Out);
    IO.WriteString(Out, "         SymInd: ");
    IO.WriteInt(Out, SOAG.SymOcc[s].SymInd);
    IO.WriteLn(Out);
    IO.WriteString(Out, "        RuleInd: ");
    IO.WriteInt(Out, SOAG.SymOcc[s].RuleInd);
    IO.WriteLn(Out);
    IO.WriteString(Out, "           Next: ");
    IO.WriteInt(Out, SOAG.SymOcc[s].Next);
    IO.WriteLn(Out);
    IO.WriteString(Out, "     AffOcc.Beg: ");
    IO.WriteInt(Out, SOAG.SymOcc[s].AffOcc.Beg);
    IO.WriteLn(Out);
    IO.WriteString(Out, "           .End: ");
    IO.WriteInt(Out, SOAG.SymOcc[s].AffOcc.End);
    IO.WriteLn(Out);
}

void WriteRuleData(int r)
{
    IO.WriteString(Out, "Rule[");
    IO.WriteInt(Out, r);
    IO.WriteText(Out, "]:\n");
    IO.WriteString(Out, "     SymOcc.Beg: ");
    IO.WriteInt(Out, SOAG.Rule[r].SymOcc.Beg);
    IO.WriteLn(Out);
    IO.WriteString(Out, "           .End: ");
    IO.WriteInt(Out, SOAG.Rule[r].SymOcc.End);
    IO.WriteLn(Out);
    IO.WriteString(Out, "     AffOcc.Beg: ");
    IO.WriteInt(Out, SOAG.Rule[r].AffOcc.Beg);
    IO.WriteLn(Out);
    IO.WriteString(Out, "           .End: ");
    IO.WriteInt(Out, SOAG.Rule[r].AffOcc.End);
    IO.WriteLn(Out);
}

void WriteRule(int r)
{
    int i;
    IO.WriteString(Out, "Rule ");
    IO.WriteInt(Out, r);
    IO.WriteString(Out, " : ");
    for (i = SOAG.Rule[r].SymOcc.Beg; i <= SOAG.Rule[r].SymOcc.End; ++i)
    {
        WriteSymOcc(i);
        if (i == SOAG.Rule[r].SymOcc.Beg)
        {
            IO.WriteString(Out, " : ");
        }
    }
    IO.WriteText(Out, ".\n");
    if (Level >= outRuleData)
    {
        WriteRuleData(r);
    }
    if (Level >= outSymOccData)
    {
        for (i = SOAG.Rule[r].SymOcc.Beg; i <= SOAG.Rule[r].SymOcc.End; ++i)
        {
            WriteSymOccData(i);
        }
    }
    if (Level >= outAffOccData)
    {
        for (i = SOAG.Rule[r].AffOcc.Beg; i <= SOAG.Rule[r].AffOcc.End; ++i)
        {
            WriteAffOccData(i);
        }
    }
}

void WriteRules()
{
    int i;
    IO.Update(Out);
    for (i = SOAG.firstRule; i <= SOAG.NextRule - 1; ++i)
    {
        WriteRule(i);
        IO.Update(Out);
    }
}

void WriteRulesL2()
{
    Level = outRuleData;
    WriteRules;
}

void WriteRulesL3()
{
    Level = outSymOccData;
    WriteRules;
}

void WriteRulesL4()
{
    Level = outAffOccData;
    WriteRules;
}

void WriteSymOccs()
{
    int i;
    for (i = SOAG.firstSymOcc; i <= SOAG.NextSymOcc - 1; ++i)
    {
        WriteSymOccData(i);
        IO.Update(Out);
    }
}

void WriteAffOccs()
{
    int i;
    for (i = SOAG.firstAffOcc; i <= SOAG.NextAffOcc - 1; ++i)
    {
        WriteAffOccData(i);
        IO.Update(Out);
    }
}

void WriteTDP(int r)
{
    int i;
    int j;
    if (SOAG.IsEvaluatorRule(r))
    {
        for (i = SOAG.Rule[r].AffOcc.Beg; i <= SOAG.Rule[r].AffOcc.End; ++i)
        {
            IO.WriteInt(Out, i - SOAG.Rule[r].AffOcc.Beg);
            IO.WriteString(Out, " | ");
            if (EAG.ParamBuf[SOAG.AffOcc[i].ParamBufInd].isDef)
            {
                IO.WriteString(Out, "DEF ");
            }
            else
            {
                IO.WriteString(Out, "APPL");
            }
            IO.WriteString(Out, " | ");
            EAG.WriteHNont(Out, SOAG.SymOcc[SOAG.AffOcc[i].SymOccInd].SymInd);
            IO.WriteString(Out, " | {");
            for (j = SOAG.Rule[r].AffOcc.Beg; j <= SOAG.Rule[r].AffOcc.End; ++j)
            {
                if (Sets.In(SOAG.Rule[r].TDP[SOAG.AffOcc[i].AffOccNum.InRule],
                        SOAG.AffOcc[j].AffOccNum.InRule))
                {
                    IO.WriteInt(Out, SOAG.AffOcc[j].AffOccNum.InRule);
                    IO.WriteString(Out, " ");
                }
            }
            IO.WriteText(Out, "}\n");
        }
    }
    else
    {
        IO.WriteInt(Out, r);
        IO.WriteText(Out, " is not an evaluator rule\n");
    }
    IO.Update(Out);
}

void WriteTDPs()
{
    int i;
    for (i = SOAG.firstRule; i <= SOAG.NextRule - 1; ++i)
    {
        WriteRule(i);
        WriteTDP(i);
    }
}

void WriteVSRule(int R)
{
    int i;
    SOAG.Instruction I;
    if (SOAG.Rule[R].VS.Beg > SOAG.Rule[R].VS.End)
    {
        IO.WriteString(Out, "keine Visit-Sequenzen; Regel: ");
        IO.WriteInt(Out, R);
    }
    else
    {
        for (i = SOAG.Rule[R].VS.Beg; i <= SOAG.Rule[R].VS.End; ++i)
        {
            I = SOAG.VS[i];

            if (cast(SOAG.Visit) I !is null)
            {
                IO.WriteString(Out, "Visit;   SymOcc: ");
                IO.WriteInt(Out, (cast(SOAG.Visit) I).SymOcc);
                IO.WriteString(Out, " VisitNo: ");
                IO.WriteInt(Out, (cast(SOAG.Visit) I).VisitNo);
            }
            else if (cast(SOAG.Leave) I !is null)
            {
                IO.WriteString(Out, "Leave; SymOcc: ");
                IO.WriteString(Out, " VisitNo: ");
                IO.WriteInt(Out, (cast(SOAG.Leave) I).VisitNo);
            }
            else if (cast(SOAG.Call) I !is null)
            {
                IO.WriteString(Out, "Call; SymOcc: ");
                IO.WriteInt(Out, (cast(SOAG.Call) I).SymOcc);
            }
            else
            {
                IO.WriteString(Out, "NOP;");
            }
            IO.WriteLn(Out);
            IO.Update(Out);
        }
    }
}

void WriteVS()
{
    int r;
    for (r = SOAG.firstRule; r <= SOAG.NextRule - 1; ++r)
    {
        WriteVSRule(r);
        IO.WriteLn(Out);
        IO.Update(Out);
    }
}

void CheckVS()
{
    int i;
    int j;
    int r;
    bool found;
    found = false;
    for (r = SOAG.firstRule; r <= SOAG.NextRule - 1; ++r)
    {
        for (i = SOAG.Rule[r].VS.Beg; i <= SOAG.Rule[r].VS.End; ++i)
        {
            for (j = SOAG.Rule[r].VS.Beg; j <= SOAG.Rule[r].VS.End; ++j)
            {
                if (i != j)
                {
                    if (SOAG.isEqual(SOAG.VS[i], SOAG.VS[j]))
                    {
                        IO.WriteText(Out, "Doppelter VS-Eintrag:\nRegel: ");
                        IO.WriteInt(Out, r);
                        IO.WriteLn(Out);
                        WriteVSRule(r);
                    }
                }
            }
        }
    }
    if (!found)
    {
        IO.WriteText(Out, "kein Doppelter VS-Eintrag gefunden.\n");
        IO.Update(Out);
    }
}

void WriteAffPos(int SymInd)
{
    int i;
    for (i = SOAG.Sym[SymInd].AffPos.Beg; i <= SOAG.Sym[SymInd].AffPos.End; ++i)
    {
        IO.WriteString(Out, "  AffixPos");
        IO.WriteInt(Out, i);
        IO.WriteLn(Out);
        IO.WriteString(Out, "    PartNum: ");
        IO.WriteInt(Out, SOAG.PartNum[i]);
        if (SOAG.StorageName != null)
        {
            IO.WriteString(Out, "    StorageType: ");
            if (SOAG.StorageName[i] < 0)
            {
                IO.WriteString(Out, "GlobalVar");
                IO.WriteInt(Out, -SOAG.StorageName[i]);
            }
            else if (SOAG.StorageName[i] > 0)
            {
                IO.WriteString(Out, "Stack");
                IO.WriteInt(Out, SOAG.StorageName[i]);
            }
            else
            {
                IO.WriteString(Out, "normal");
            }
        }
        IO.WriteLn(Out);
        IO.Update(Out);
    }
}

void WriteSym(int S)
{
    IO.WriteText(Out, "Symbol ");
    EAG.WriteHNont(Out, SOAG.SymOcc[SOAG.Sym[S].FirstOcc].SymInd);
    IO.WriteText(Out, ": \nFirstOcc: ");
    IO.WriteInt(Out, SOAG.Sym[S].FirstOcc);
    IO.WriteLn(Out);
    WriteAffPos(S);
    IO.WriteString(Out, "MaxPart: ");
    IO.WriteInt(Out, SOAG.Sym[S].MaxPart);
    IO.WriteLn(Out);
    IO.Update(Out);
}

void WriteSyms()
{
    int i;
    for (i = SOAG.firstSym; i <= SOAG.NextSym - 1; ++i)
    {
        WriteSym(i);
    }
}

static this()
{
    Out = IO.Msg;
    Level = standardLevel;
}

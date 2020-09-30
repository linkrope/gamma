module soag.eSOAGProtocol;

import EAG = eEAG;
import IO = eIO;
import Scanner = eScanner;
import Sets = eSets;
import runtime;
import SOAG = soag.eSOAG;

const standardLevel = 1;
const outRuleData = 2;
const outSymOccData = 3;
const outAffOccData = 4;
int Level;
IO.TextOut Out;

void WriteAffixVariables(int i)
{
    if (i < 0)
    {
        if (EAG.Var[-i].Num < 0)
        {
            Out.write("#");
        }
        Out.write(EAG.VarRepr(-i));
        Out.write(EAG.Var[-i].Num);
    }
    else
    {
        for (int MA = 1; MA <= EAG.MAlt[EAG.NodeBuf[i]].Arity; ++MA)
        {
            WriteAffixVariables(EAG.NodeBuf[i + MA]);
        }
    }
}

void WriteAffix(int i)
{
    if (i < 0)
    {
        if (EAG.Var[-i].Num < 0)
        {
            Out.write("#");
        }
        Out.write(EAG.VarRepr(-i));
        Out.write("(");
        Out.write(EAG.Var[-i].Num);
        Out.write(") ");
    }
    else
    {
        int a = 0;
        int m = EAG.MAlt[EAG.NodeBuf[i]].Right;

        while (EAG.MembBuf[m] != EAG.nil)
        {
            if (EAG.MembBuf[m] < 0)
            {
                Out.write(Scanner.repr(EAG.MTerm[-EAG.MembBuf[m]].Id));
                Out.write(" ");
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
        Out.write("-");
    }
    else
    {
        Out.write("+");
    }
    if (EAG.ParamBuf[p].Affixform < 0)
    {
        Out.write(EAG.VarRepr(-EAG.ParamBuf[p].Affixform));
        Out.write("(");
        Out.write(EAG.Var[-EAG.ParamBuf[p].Affixform].Num);
        Out.write(") ");
    }
    else
    {
        WriteAffix(EAG.ParamBuf[p].Affixform);
    }
    if (EAG.ParamBuf[p + 1].Affixform != EAG.nil)
    {
        Out.write(", ");
    }
}

void WriteSymOcc(int s)
{
    Out.write(EAG.HNontRepr(SOAG.SymOcc[s].SymInd));
    Out.write("< ");
    for (int i = SOAG.SymOcc[s].AffOcc.Beg; i <= SOAG.SymOcc[s].AffOcc.End; ++i)
    {
        WriteAffOcc(i);
    }
    Out.write(" >");
    Out.flush;
}

void WriteAffOccData(int s)
{
    Out.write("AffOcc[");
    Out.write(s);
    Out.write("]: ");
    WriteAffOcc(s);
    Out.writeln;
    Out.write("  Variables: ");
    WriteAffixVariables(EAG.ParamBuf[SOAG.AffOcc[s].ParamBufInd].Affixform);
    Out.writeln;
    Out.write("         ParamBufInd: ");
    Out.write(SOAG.AffOcc[s].ParamBufInd);
    Out.writeln;
    Out.write("           SymOccInd: ");
    Out.write(SOAG.AffOcc[s].SymOccInd);
    Out.writeln;
    Out.write("    AffOccNum.InRule: ");
    Out.write(SOAG.AffOcc[s].AffOccNum.InRule);
    Out.writeln;
    Out.write("     AffOccNum.InSym: ");
    Out.write(SOAG.AffOcc[s].AffOccNum.InSym);
    Out.writeln;
}

void WriteSymOccData(int s)
{
    Out.write("SymOcc[");
    Out.write(s);
    Out.write("]: ");
    WriteSymOcc(s);
    Out.writeln;
    Out.write("         SymInd: ");
    Out.write(SOAG.SymOcc[s].SymInd);
    Out.writeln;
    Out.write("        RuleInd: ");
    Out.write(SOAG.SymOcc[s].RuleInd);
    Out.writeln;
    Out.write("           Next: ");
    Out.write(SOAG.SymOcc[s].Next);
    Out.writeln;
    Out.write("     AffOcc.Beg: ");
    Out.write(SOAG.SymOcc[s].AffOcc.Beg);
    Out.writeln;
    Out.write("           .End: ");
    Out.write(SOAG.SymOcc[s].AffOcc.End);
    Out.writeln;
}

void WriteRuleData(int r)
{
    Out.write("Rule[");
    Out.write(r);
    Out.write("]:\n");
    Out.write("     SymOcc.Beg: ");
    Out.write(SOAG.Rule[r].SymOcc.Beg);
    Out.writeln;
    Out.write("           .End: ");
    Out.write(SOAG.Rule[r].SymOcc.End);
    Out.writeln;
    Out.write("     AffOcc.Beg: ");
    Out.write(SOAG.Rule[r].AffOcc.Beg);
    Out.writeln;
    Out.write("           .End: ");
    Out.write(SOAG.Rule[r].AffOcc.End);
    Out.writeln;
}

void WriteRule(int r)
{
    int i;
    Out.write("Rule ");
    Out.write(r);
    Out.write(" : ");
    for (i = SOAG.Rule[r].SymOcc.Beg; i <= SOAG.Rule[r].SymOcc.End; ++i)
    {
        WriteSymOcc(i);
        if (i == SOAG.Rule[r].SymOcc.Beg)
        {
            Out.write(" : ");
        }
    }
    Out.write(".\n");
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
    Out.flush;
    for (i = SOAG.firstRule; i <= SOAG.NextRule - 1; ++i)
    {
        WriteRule(i);
        Out.flush;
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
        Out.flush;
    }
}

void WriteAffOccs()
{
    int i;
    for (i = SOAG.firstAffOcc; i <= SOAG.NextAffOcc - 1; ++i)
    {
        WriteAffOccData(i);
        Out.flush;
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
            Out.write(i - SOAG.Rule[r].AffOcc.Beg);
            Out.write(" | ");
            if (EAG.ParamBuf[SOAG.AffOcc[i].ParamBufInd].isDef)
            {
                Out.write("DEF ");
            }
            else
            {
                Out.write("APPL");
            }
            Out.write(" | ");
            Out.write(EAG.HNontRepr(SOAG.SymOcc[SOAG.AffOcc[i].SymOccInd].SymInd));
            Out.write(" | {");
            for (j = SOAG.Rule[r].AffOcc.Beg; j <= SOAG.Rule[r].AffOcc.End; ++j)
            {
                if (Sets.In(SOAG.Rule[r].TDP[SOAG.AffOcc[i].AffOccNum.InRule],
                        SOAG.AffOcc[j].AffOccNum.InRule))
                {
                    Out.write(SOAG.AffOcc[j].AffOccNum.InRule);
                    Out.write(" ");
                }
            }
            Out.write("}\n");
        }
    }
    else
    {
        Out.write(r);
        Out.write(" is not an evaluator rule\n");
    }
    Out.flush;
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
        Out.write("keine Visit-Sequenzen; Regel: ");
        Out.write(R);
    }
    else
    {
        for (i = SOAG.Rule[R].VS.Beg; i <= SOAG.Rule[R].VS.End; ++i)
        {
            I = SOAG.VS[i];

            if (cast(SOAG.Visit) I !is null)
            {
                Out.write("Visit;   SymOcc: ");
                Out.write((cast(SOAG.Visit) I).SymOcc);
                Out.write(" VisitNo: ");
                Out.write((cast(SOAG.Visit) I).VisitNo);
            }
            else if (cast(SOAG.Leave) I !is null)
            {
                Out.write("Leave; SymOcc: ");
                Out.write(" VisitNo: ");
                Out.write((cast(SOAG.Leave) I).VisitNo);
            }
            else if (cast(SOAG.Call) I !is null)
            {
                Out.write("Call; SymOcc: ");
                Out.write((cast(SOAG.Call) I).SymOcc);
            }
            else
            {
                Out.write("NOP;");
            }
            Out.writeln;
            Out.flush;
        }
    }
}

void WriteVS()
{
    int r;
    for (r = SOAG.firstRule; r <= SOAG.NextRule - 1; ++r)
    {
        WriteVSRule(r);
        Out.writeln;
        Out.flush;
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
                        Out.write("Doppelter VS-Eintrag:\nRegel: ");
                        Out.write(r);
                        Out.writeln;
                        WriteVSRule(r);
                    }
                }
            }
        }
    }
    if (!found)
    {
        Out.write("kein Doppelter VS-Eintrag gefunden.\n");
        Out.flush;
    }
}

void WriteAffPos(int SymInd)
{
    int i;
    for (i = SOAG.Sym[SymInd].AffPos.Beg; i <= SOAG.Sym[SymInd].AffPos.End; ++i)
    {
        Out.write("  AffixPos");
        Out.write(i);
        Out.writeln;
        Out.write("    PartNum: ");
        Out.write(SOAG.PartNum[i]);
        if (SOAG.StorageName != null)
        {
            Out.write("    StorageType: ");
            if (SOAG.StorageName[i] < 0)
            {
                Out.write("GlobalVar");
                Out.write(-SOAG.StorageName[i]);
            }
            else if (SOAG.StorageName[i] > 0)
            {
                Out.write("Stack");
                Out.write(SOAG.StorageName[i]);
            }
            else
            {
                Out.write("normal");
            }
        }
        Out.writeln;
        Out.flush;
    }
}

void WriteSym(int S)
{
    Out.write("Symbol ");
    Out.write(EAG.HNontRepr(S));
    Out.write(": \n  FirstOcc: ");
    Out.write(SOAG.Sym[S].FirstOcc);
    Out.writeln;
    WriteAffPos(S);
    Out.write("  MaxPart: ");
    Out.write(SOAG.Sym[S].MaxPart);
    Out.writeln;
    Out.flush;
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

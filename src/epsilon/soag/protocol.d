module epsilon.soag.protocol;

import EAG = epsilon.eag;
import SOAG = epsilon.soag.soag;
import runtime;
import std.stdio;

const standardLevel = 1;
const outRuleData = 2;
const outSymOccData = 3;
const outAffOccData = 4;
int Level;
File output;

void WriteAffixVariables(int i) @safe
{
    if (i < 0)
    {
        if (EAG.Var[-i].Num < 0)
        {
            output.write("!");
        }
        output.write(EAG.VarRepr(-i), EAG.Var[-i].Num);
    }
    else
    {
        for (int MA = 1; MA <= EAG.MAlt[EAG.NodeBuf[i]].Arity; ++MA)
        {
            WriteAffixVariables(EAG.NodeBuf[i + MA]);
        }
    }
}

void WriteAffix(int i) @safe
{
    if (i < 0)
    {
        if (EAG.Var[-i].Num < 0)
        {
            output.write("!");
        }
        output.write(EAG.VarRepr(-i), "(", EAG.Var[-i].Num, ") ");
    }
    else
    {
        int a = 0;
        int m = EAG.MAlt[EAG.NodeBuf[i]].Right;

        while (EAG.MembBuf[m] != EAG.nil)
        {
            if (EAG.MembBuf[m] < 0)
            {
                output.write(EAG.symbolTable.symbol(EAG.MTerm[-EAG.MembBuf[m]].Id), " ");
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

void WriteAffOcc(int a) @safe
{
    int p;
    p = SOAG.AffOcc[a].ParamBufInd;
    output.write(EAG.ParamBuf[p].isDef ? "-" : "+");
    if (EAG.ParamBuf[p].Affixform < 0)
    {
        output.write(EAG.VarRepr(-EAG.ParamBuf[p].Affixform));
        output.write("(", EAG.Var[-EAG.ParamBuf[p].Affixform].Num, ") ");
    }
    else
    {
        WriteAffix(EAG.ParamBuf[p].Affixform);
    }
    if (EAG.ParamBuf[p + 1].Affixform != EAG.nil)
        output.write(", ");
}

void WriteSymOcc(int s) @safe
{
    output.write(EAG.HNontRepr(SOAG.SymOcc[s].SymInd));
    output.write("< ");
    for (int i = SOAG.SymOcc[s].AffOcc.Beg; i <= SOAG.SymOcc[s].AffOcc.End; ++i)
    {
        WriteAffOcc(i);
    }
    output.write(" >");
    output.flush;
}

void WriteAffOccData(int s) @safe
{
    output.write("AffOcc[", s, "]: ");
    WriteAffOcc(s);
    output.writeln;
    output.write("  Variables: ");
    WriteAffixVariables(EAG.ParamBuf[SOAG.AffOcc[s].ParamBufInd].Affixform);
    output.writeln;
    output.write("         ParamBufInd: ");
    output.write(SOAG.AffOcc[s].ParamBufInd);
    output.writeln;
    output.write("           SymOccInd: ");
    output.write(SOAG.AffOcc[s].SymOccInd);
    output.writeln;
    output.write("    AffOccNum.InRule: ");
    output.write(SOAG.AffOcc[s].AffOccNum.InRule);
    output.writeln;
    output.write("     AffOccNum.InSym: ");
    output.write(SOAG.AffOcc[s].AffOccNum.InSym);
    output.writeln;
}

void WriteSymOccData(int s) @safe
{
    output.write("SymOcc[", s, "]: ");
    WriteSymOcc(s);
    output.writeln;
    output.writeln("         SymInd: ", SOAG.SymOcc[s].SymInd);
    output.writeln("        RuleInd: ", SOAG.SymOcc[s].RuleInd);
    output.writeln("           Next: ", SOAG.SymOcc[s].Next);
    output.writeln("     AffOcc.Beg: ", SOAG.SymOcc[s].AffOcc.Beg);
    output.writeln("           .End: ", SOAG.SymOcc[s].AffOcc.End);
}

void WriteRuleData(int r) @safe
{
    output.writeln("Rule[", r, "]:");
    output.writeln("     SymOcc.Beg: ", SOAG.Rule[r].SymOcc.Beg);
    output.writeln("           .End: ", SOAG.Rule[r].SymOcc.End);
    output.writeln("     AffOcc.Beg: ", SOAG.Rule[r].AffOcc.Beg);
    output.writeln("           .End: ", SOAG.Rule[r].AffOcc.End);
}

void WriteRule(int r) @safe
{
    output.write("Rule ", r, " : ");
    for (int i = SOAG.Rule[r].SymOcc.Beg; i <= SOAG.Rule[r].SymOcc.End; ++i)
    {
        WriteSymOcc(i);
        if (i == SOAG.Rule[r].SymOcc.Beg)
        {
            output.write(" : ");
        }
    }
    output.writeln(".");
    if (Level >= outRuleData)
    {
        WriteRuleData(r);
    }
    if (Level >= outSymOccData)
    {
        for (int i = SOAG.Rule[r].SymOcc.Beg; i <= SOAG.Rule[r].SymOcc.End; ++i)
        {
            WriteSymOccData(i);
        }
    }
    if (Level >= outAffOccData)
    {
        for (int i = SOAG.Rule[r].AffOcc.Beg; i <= SOAG.Rule[r].AffOcc.End; ++i)
        {
            WriteAffOccData(i);
        }
    }
}

void WriteRules() @safe
{
    output.flush;
    for (int i = SOAG.firstRule; i < SOAG.NextRule; ++i)
    {
        WriteRule(i);
        output.flush;
    }
}

void WriteRulesL2() @safe
{
    Level = outRuleData;
    WriteRules;
}

void WriteRulesL3() @safe
{
    Level = outSymOccData;
    WriteRules;
}

void WriteRulesL4() @safe
{
    Level = outAffOccData;
    WriteRules;
}

void WriteSymOccs() @safe
{
    for (int i = SOAG.firstSymOcc; i < SOAG.NextSymOcc; ++i)
    {
        WriteSymOccData(i);
        output.flush;
    }
}

void WriteAffOccs() @safe
{
    for (int i = SOAG.firstAffOcc; i < SOAG.NextAffOcc; ++i)
    {
        WriteAffOccData(i);
        output.flush;
    }
}

void WriteTDP(int r)
{
    if (SOAG.IsEvaluatorRule(r))
    {
        for (int i = SOAG.Rule[r].AffOcc.Beg; i <= SOAG.Rule[r].AffOcc.End; ++i)
        {
            output.write(i - SOAG.Rule[r].AffOcc.Beg);
            output.write(" | ");
            output.write(EAG.ParamBuf[SOAG.AffOcc[i].ParamBufInd].isDef ? "DEF " : "APPL");
            output.write(" | ");
            output.write(EAG.HNontRepr(SOAG.SymOcc[SOAG.AffOcc[i].SymOccInd].SymInd));
            output.write(" | {");
            for (int j = SOAG.Rule[r].AffOcc.Beg; j <= SOAG.Rule[r].AffOcc.End; ++j)
            {
                if (SOAG.Rule[r].TDP[SOAG.AffOcc[i].AffOccNum.InRule][SOAG.AffOcc[j].AffOccNum.InRule])
                    output.write(SOAG.AffOcc[j].AffOccNum.InRule, " ");
            }
            output.writeln("}");
        }
    }
    else
    {
        output.writeln(r, " is not an evaluator rule");
    }
}

void WriteTDPs()
{
    for (int i = SOAG.firstRule; i < SOAG.NextRule; ++i)
    {
        WriteRule(i);
        WriteTDP(i);
    }
}

void WriteVSRule(int R) @safe
{
    if (SOAG.Rule[R].VS.Beg > SOAG.Rule[R].VS.End)
    {
        output.write("keine Visit-Sequenzen; Regel: ", R);
    }
    else
    {
        foreach (i; SOAG.Rule[R].VS.Beg .. SOAG.Rule[R].VS.End + 1)
        {
            SOAG.Instruction I = SOAG.VS[i];

            if (auto visit = cast(SOAG.Visit) I)
            {
                output.write("Visit;   SymOcc: ", visit.SymOcc);
                output.write(" VisitNo: ", visit.VisitNo);
            }
            else if (auto leave = cast(SOAG.Leave) I)
            {
                output.write("Leave; SymOcc: ");
                output.write(" VisitNo: ", leave.VisitNo);
            }
            else if (auto call = cast(SOAG.Call) I)
            {
                output.write("Call; SymOcc: ", call.SymOcc);
            }
            else
            {
                output.write("NOP;");
            }
            output.writeln;
            output.flush;
        }
    }
}

void WriteVS() @safe
{
    foreach (r; SOAG.firstRule .. SOAG.NextRule)
    {
        WriteVSRule(r);
        output.writeln;
        output.flush;
    }
}

void CheckVS() @safe
{
    bool found = false;

    foreach (r; SOAG.firstRule .. SOAG.NextRule)
    {
        foreach (i; SOAG.Rule[r].VS.Beg .. SOAG.Rule[r].VS.End + 1)
        {
            foreach (j; SOAG.Rule[r].VS.Beg .. SOAG.Rule[r].VS.End + 1)
            {
                if (i != j)
                {
                    if (SOAG.isEqual(SOAG.VS[i], SOAG.VS[j]))
                    {
                        found = true;
                        output.writeln("Doppelter VS-Eintrag:");
                        output.writeln("Regel: ", r);
                        WriteVSRule(r);
                    }
                }
            }
        }
    }
    if (!found)
        output.writeln("kein Doppelter VS-Eintrag gefunden.");
}

void WriteAffPos(int SymInd) @safe
{
    for (int i = SOAG.Sym[SymInd].AffPos.Beg; i <= SOAG.Sym[SymInd].AffPos.End; ++i)
    {
        output.writeln("  AffixPos", i);
        output.write("    PartNum: ", SOAG.PartNum[i]);
        if (SOAG.StorageName != null)
        {
            output.write("    StorageType: ");
            if (SOAG.StorageName[i] < 0)
                output.write("GlobalVar", -SOAG.StorageName[i]);
            else if (SOAG.StorageName[i] > 0)
                output.write("Stack", SOAG.StorageName[i]);
            else
                output.write("normal");
        }
        output.writeln;
    }
}

void WriteSym(int S) @safe
{
    output.writeln("Symbol ", EAG.HNontRepr(S), ":");
    output.writeln("  FirstOcc: ", SOAG.Sym[S].FirstOcc);
    WriteAffPos(S);
    output.writeln("  MaxPart: ", SOAG.Sym[S].MaxPart);
}

void WriteSyms() @safe
{
    foreach (i; SOAG.firstSym .. SOAG.NextSym)
        WriteSym(i);
}

static this() nothrow
{
    output = stdout;
    Level = standardLevel;
}

module epsilon.emitgen;

import EAG = epsilon.eag;
import epsilon.settings;
import runtime;
import std.bitmanip : BitArray;
import std.stdio;

const CaseLabels = 127;
BitArray Type3;
BitArray Type2;
int StartMNont;

void GenEmitProc(File Mod, Settings settings)
{
    void CalcSets(int Nont)
    in (EAG.firstMNont <= Nont)
    in (Nont < EAG.NextMNont)
    {
        int A;
        int F;
        int M;

        if (EAG.MNont[Nont].IsToken)
            Type3[Nont] = true;
        A = EAG.MNont[Nont].MRule;
        while (A != EAG.nil)
        {
            F = EAG.MAlt[A].Right;
            while (EAG.MembBuf[F] != EAG.nil)
            {
                M = EAG.MembBuf[F];
                if (M > 0)
                {
                    if (Type3[Nont] && !Type3[M])
                    {
                        Type3[M] = true;
                        CalcSets(M);
                    }
                    if (Type2[Nont] && !Type2[M])
                    {
                        if (!EAG.MNont[M].IsToken)
                            Type2[M] = true;
                        CalcSets(M);
                    }
                }
                ++F;
            }
            A = EAG.MAlt[A].Next;
        }
    }

    void GenEmitProcs(BitArray MNonts)
    {
        void GenProcName(size_t N, BitArray Type)
        {
            Mod.write("Emit");
            Mod.write(N);
            Mod.write("Type");
            if (Type == Type2)
                Mod.write('2');
            else
                Mod.write('3');
        }

        void GenAlts(size_t N)
        {
            int A;
            int F;
            int M;
            int arity;
            int ANum;

            void WhiteSpace()
            {
                if (settings.space)
                    Mod.write("Out.write(' '); ");
                else
                    Mod.write("Out.writeln; ");
            }

            A = EAG.MNont[N].MRule;
            ANum = 1;
            Mod.write("switch (MOD(Heap[Ptr], arityConst))\n");
            Mod.write("{\n");
            while (A != EAG.nil)
            {
                if (ANum > CaseLabels)
                {
                    stdout.write("internal error: Too many meta alts in ");
                    stdout.write(EAG.symbolTable.symbol(EAG.MTerm[N].Id));
                    stdout.writeln;
                    assert(0);
                }
                F = EAG.MAlt[A].Right;
                arity = 0;
                Mod.write("case ");
                Mod.write(ANum);
                Mod.write(":\n");
                while (EAG.MembBuf[F] != EAG.nil)
                {
                    M = EAG.MembBuf[F];
                    if (M < 0)
                    {
                        Mod.write("Out.write(");
                        Mod.write(EAG.symbolTable.symbol(EAG.MTerm[-M].Id));
                        Mod.write("); ");
                        if (MNonts == Type2)
                            WhiteSpace;
                    }
                    else
                    {
                        if (MNonts == Type3 || EAG.MNont[M].IsToken)
                            GenProcName(M, Type3);
                        else
                            GenProcName(M, Type2);
                        ++arity;
                        Mod.write("(Heap[Ptr + ");
                        Mod.write(arity);
                        Mod.write("]); ");
                        if (EAG.MNont[M].IsToken && MNonts == Type2)
                            WhiteSpace;
                    }
                    ++F;
                    Mod.writeln;
                }
                Mod.write("break;\n");
                A = EAG.MAlt[A].Next;
                ++ANum;
            }
            Mod.write("default:\n");
            Mod.write("Out.write(Heap[Ptr]);\n");
            Mod.write("}\n");
        }

        foreach (N; MNonts.bitsSet)
        {
            Mod.write("void ");
            GenProcName(N, MNonts);
            Mod.write("(HeapType Ptr)\n");
            Mod.write("{\n");
            Mod.write("OutputSize += DIV(MOD(Heap[Ptr], refConst), arityConst) + 1;\n");
            GenAlts(N);
            Mod.write("}\n\n");
        }
    }

    StartMNont = EAG.DomBuf[EAG.HNont[EAG.StartSym].Sig];
    Type3 = BitArray();
    Type3.length = EAG.NextMNont + 1;
    Type2 = BitArray();
    Type2.length = EAG.NextMNont + 1;
    if (!EAG.MNont[StartMNont].IsToken)
        Type2[StartMNont] = true;
    CalcSets(StartMNont);
    if (!Type3.bitsSet.empty)
        GenEmitProcs(Type3);
    if (!Type2.bitsSet.empty)
        GenEmitProcs(Type2);
}

void GenShowHeap(File Mod) @safe
{
    Mod.write("if (info_)\n");
    Mod.write("{\n");
    Mod.write("stdout.write(\"    tree of \"); ");
    Mod.write("stdout.write(OutputSize); \n");
    Mod.write("stdout.write(\" uses \"); stdout.write(CountHeap());");
    Mod.write("stdout.write(\" of \"); \n");
    Mod.write("stdout.write(NextHeap);  stdout.write(\" allocated, with \"); ");
    Mod.write("stdout.write(predefined + 1);\n");
    Mod.write("stdout.write(\" predefined\\n\");\n");
    Mod.write("}\n");
}

void GenEmitCall(File Mod, Settings settings)
{
    Mod.write("if (");
    if (settings.write)
        Mod.write("!");
    Mod.write("write)\n");
    Mod.write(`Out = File("`);
    Mod.write(EAG.BaseName);
    Mod.write(`.Out", "w");`);
    Mod.write("\nelse\n");
    Mod.write("Out = stdout;\n");
    Mod.write("Emit");
    Mod.write(StartMNont);
    Mod.write("Type");
    if (Type2[StartMNont])
        Mod.write('2');
    else
        Mod.write('3');
    Mod.write("(V1); Out.writeln; Out.flush;\n");
}

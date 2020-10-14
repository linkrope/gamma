module eEmitGen;

import EAG = eEAG;
import IO = eIO;
import Scanner = eScanner;
import epsilon.settings;
import runtime;
import std.bitmanip : BitArray;

const CaseLabels = 127;
BitArray Type3;
BitArray Type2;
int StartMNont;

void GenEmitProc(IO.TextOut Mod, Settings settings)
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
        int N;

        void GenProcName(int N, BitArray Type)
        {
            Mod.write("Emit");
            Mod.write(N);
            Mod.write("Type");
            if (Type == Type2)
            {
                Mod.write('2');
            }
            else
            {
                Mod.write('3');
            }
        }

        void GenAlts(int N)
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
                    IO.Msg.write("internal error: Too many meta alts in ");
                    IO.Msg.write(Scanner.repr(EAG.MTerm[N].Id));
                    IO.Msg.writeln;
                    IO.Msg.flush;
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
                        Mod.write(Scanner.repr(EAG.MTerm[-M].Id));
                        Mod.write("); ");
                        if (MNonts == Type2)
                        {
                            WhiteSpace;
                        }
                    }
                    else
                    {
                        if (MNonts == Type3 || EAG.MNont[M].IsToken)
                        {
                            GenProcName(M, Type3);
                        }
                        else
                        {
                            GenProcName(M, Type2);
                        }
                        ++arity;
                        Mod.write("(Heap[Ptr + ");
                        Mod.write(arity);
                        Mod.write("]); ");
                        if (EAG.MNont[M].IsToken && MNonts == Type2)
                        {
                            WhiteSpace;
                        }
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

        // TODO: foreach (N; MNonts)
        for (N = EAG.firstMNont; N < EAG.NextMNont; ++N)
        {
            if (MNonts[N])
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

void GenShowHeap(IO.TextOut Mod)
{
    Mod.write("if (info)\n");
    Mod.write("{\n");
    Mod.write("IO.Msg.write(\"    tree of \"); ");
    Mod.write("IO.Msg.write(OutputSize); \n");
    Mod.write("IO.Msg.write(\" uses \"); IO.Msg.write(CountHeap());");
    Mod.write("IO.Msg.write(\" of \"); \n");
    Mod.write("IO.Msg.write(NextHeap);  IO.Msg.write(\" allocated, with \"); ");
    Mod.write("IO.Msg.write(predefined + 1);\n");
    Mod.write("IO.Msg.write(\" predefined\\n\"); IO.Msg.flush;\n");
    Mod.write("}\n");
}

void GenEmitCall(IO.TextOut Mod, Settings settings)
{
    Mod.write("if (");
    if (settings.write)
        Mod.write("!");
    Mod.write("write)\n");
    Mod.write("Out = new IO.TextOut(\"");
    Mod.write(EAG.BaseName);
    Mod.write(".Out\");\n");
    Mod.write("else\n");
    Mod.write("Out = IO.Msg;\n");
    Mod.write("Emit");
    Mod.write(StartMNont);
    Mod.write("Type");
    if (Type2[StartMNont])
        Mod.write('2');
    else
        Mod.write('3');
    Mod.write("(V1); Out.writeln; Out.flush;\n");
}

module eEmitGen;

import runtime;
import Sets = eSets;
import IO = eIO;
import Scanner = eScanner;
import EAG = eEAG;

const CaseLabels = 127;
Sets.OpenSet Type3;
Sets.OpenSet Type2;
int StartMNont;

void GenEmitProc(IO.TextOut Mod)
{
    int Lo;
    int Hi;
    bool EmitSpace;

    void CalcSets(int Nont)
    in (EAG.firstMNont <= Nont)
    in (Nont < EAG.NextMNont)
    {
        int A;
        int F;
        int M;

        if (EAG.MNont[Nont].IsToken)
        {
            Sets.Incl(Type3, Nont);
        }
        A = EAG.MNont[Nont].MRule;
        while (A != EAG.nil)
        {
            F = EAG.MAlt[A].Right;
            while (EAG.MembBuf[F] != EAG.nil)
            {
                M = EAG.MembBuf[F];
                if (M > 0)
                {
                    if (Sets.In(Type3, Nont) && !Sets.In(Type3, M))
                    {
                        Sets.Incl(Type3, M);
                        CalcSets(M);
                    }
                    if (Sets.In(Type2, Nont) && !Sets.In(Type2, M))
                    {
                        if (!EAG.MNont[M].IsToken)
                        {
                            Sets.Incl(Type2, M);
                        }
                        CalcSets(M);
                    }
                }
                ++F;
            }
            A = EAG.MAlt[A].Next;
        }
    }

    void GenEmitProcs(Sets.OpenSet MNonts)
    {
        int N;

        void GenProcName(int N, Sets.OpenSet Type)
        {
            IO.WriteString(Mod, "Emit");
            IO.WriteInt(Mod, N);
            IO.WriteString(Mod, "Type");
            if (Type == Type2)
            {
                IO.Write(Mod, '2');
            }
            else
            {
                IO.Write(Mod, '3');
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
                if (EmitSpace)
                {
                    IO.WriteString(Mod, "IO.Write(Out, ' '); ");
                }
                else
                {
                    IO.WriteString(Mod, "IO.WriteLn(Out); ");
                }
            }

            A = EAG.MNont[N].MRule;
            ANum = 1;
            IO.WriteText(Mod, "switch (MOD(Heap[Ptr], arityConst))\n");
            IO.WriteText(Mod, "{\n");
            while (A != EAG.nil)
            {
                if (ANum > CaseLabels)
                {
                    IO.WriteString(IO.Msg, "internal error: Too many meta alts in ");
                    Scanner.WriteRepr(IO.Msg, EAG.MTerm[N].Id);
                    IO.WriteLn(IO.Msg);
                    IO.Update(IO.Msg);
                    assert(0);
                }
                F = EAG.MAlt[A].Right;
                arity = 0;
                IO.WriteText(Mod, "case ");
                IO.WriteInt(Mod, ANum);
                IO.WriteText(Mod, ":\n");
                while (EAG.MembBuf[F] != EAG.nil)
                {
                    M = EAG.MembBuf[F];
                    if (M < 0)
                    {
                        IO.WriteText(Mod, "IO.WriteText(Out, ");
                        Scanner.WriteRepr(Mod, EAG.MTerm[-M].Id);
                        IO.WriteText(Mod, "); ");
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
                        IO.WriteText(Mod, "(Heap[Ptr + ");
                        IO.WriteInt(Mod, arity);
                        IO.WriteString(Mod, "]); ");
                        if (EAG.MNont[M].IsToken && MNonts == Type2)
                        {
                            WhiteSpace;
                        }
                    }
                    ++F;
                    IO.WriteLn(Mod);
                }
                IO.WriteText(Mod, "break;\n");
                A = EAG.MAlt[A].Next;
                ++ANum;
            }
            IO.WriteText(Mod, "default:\n");
            IO.WriteText(Mod, "IO.WriteInt(Out, Heap[Ptr]);\n");
            IO.WriteText(Mod, "}\n");
        }

        for (N = EAG.firstMNont; N <= EAG.NextMNont - 1; ++N)
        {
            if (Sets.In(MNonts, N))
            {
                IO.WriteText(Mod, "// ");
                IO.WriteText(Mod, "PROCEDURE ^ ");
                GenProcName(N, MNonts);
                IO.WriteText(Mod, "(Ptr: HeapType);\n");
            }
        }
        IO.WriteLn(Mod);
        for (N = EAG.firstMNont; N <= EAG.NextMNont - 1; ++N)
        {
            if (Sets.In(MNonts, N))
            {
                IO.WriteText(Mod, "void ");
                GenProcName(N, MNonts);
                IO.WriteText(Mod, "(HeapType Ptr)\n");
                IO.WriteText(Mod, "{\n");
                IO.WriteText(Mod, "OutputSize += DIV(MOD(Heap[Ptr], refConst), arityConst) + 1;\n");
                GenAlts(N);
                IO.WriteText(Mod, "}\n\n");
            }
        }
    }

    EmitSpace = IO.IsOption('s');
    StartMNont = EAG.DomBuf[EAG.HNont[EAG.StartSym].Sig];
    Sets.New(Type3, EAG.NextMNont);
    Sets.New(Type2, EAG.NextMNont);
    if (!EAG.MNont[StartMNont].IsToken)
    {
        Sets.Incl(Type2, StartMNont);
    }
    CalcSets(StartMNont);
    if (!Sets.IsEmpty(Type3))
    {
        GenEmitProcs(Type3);
    }
    if (!Sets.IsEmpty(Type2))
    {
        GenEmitProcs(Type2);
    }
}

void GenShowHeap(IO.TextOut Mod)
{
    IO.WriteText(Mod, "if (IO.IsOption('i'))\n");
    IO.WriteText(Mod, "{\n");
    IO.WriteText(Mod, "IO.WriteText(IO.Msg, \"    tree of \"); ");
    IO.WriteText(Mod, "IO.WriteInt(IO.Msg, OutputSize); \n");
    IO.WriteString(Mod, "IO.WriteText(IO.Msg, \" uses \"); IO.WriteInt(IO.Msg, CountHeap());");
    IO.WriteText(Mod, "IO.WriteText(IO.Msg, \" of \"); \n");
    IO.WriteString(Mod,"IO.WriteInt(IO.Msg, NextHeap);  IO.WriteText(IO.Msg, \" allocated, with \"); ");
    IO.WriteText(Mod, "IO.WriteInt(IO.Msg, predefined + 1);\n");
    IO.WriteText(Mod, "IO.WriteText(IO.Msg, \" predefined\\n\"); IO.Update(IO.Msg);\n");
    IO.WriteText(Mod, "}\n");
}

void GenEmitCall(IO.TextOut Mod)
{
    IO.WriteText(Mod, "if (");
    if (IO.IsOption('w'))
    {
        IO.WriteText(Mod, "!");
    }
    IO.WriteText(Mod, "IO.IsOption('w'))\n");
    IO.WriteText(Mod, "IO.CreateOut(Out, \"");
    IO.WriteString(Mod, EAG.BaseName);
    IO.WriteText(Mod, ".Out\");\n");
    IO.WriteText(Mod, "else\n");
    IO.WriteText(Mod, "Out = IO.Msg;\n");
    IO.WriteString(Mod, "Emit");
    IO.WriteInt(Mod, StartMNont);
    IO.WriteString(Mod, "Type");
    if (Sets.In(Type2, StartMNont))
    {
        IO.Write(Mod, '2');
    }
    else
    {
        IO.Write(Mod, '3');
    }
    IO.WriteText(Mod, "(V1); IO.WriteLn(Out); IO.Update(Out);\n");
}

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
    {
        int A;
        int F;
        int M;
        ASSERT(Nont >= EAG.firstMNont, 98);
        ASSERT(Nont < EAG.NextMNont, 97);
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
                IO.Write(Mod, "2");
            }
            else
            {
                IO.Write(Mod, "3");
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
            IO.WriteText(Mod, "\tCASE Heap[Ptr] MOD arityConst OF \n");
            while (A != EAG.nil)
            {
                if (ANum > CaseLabels)
                {
                    IO.WriteString(IO.Msg, "internal error: Too many metaalts in ");
                    Scanner.WriteRepr(IO.Msg, EAG.MTerm[N].Id);
                    IO.WriteLn(IO.Msg);
                    IO.Update(IO.Msg);
                    HALT(99);
                }
                F = EAG.MAlt[A].Right;
                arity = 0;
                IO.WriteText(Mod, "\t| ");
                IO.WriteInt(Mod, ANum);
                IO.WriteText(Mod, ": ");
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
                }
                IO.WriteLn(Mod);
                A = EAG.MAlt[A].Next;
                ++ANum;
            }
            IO.WriteText(Mod, "\tELSE IO.WriteInt(Out, Heap[Ptr]) \n\tEND \n");
        }

        for (N = EAG.firstMNont; N <= EAG.NextMNont - 1; ++N)
        {
            if (Sets.In(MNonts, N))
            {
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
                IO.WriteText(Mod, "PROCEDURE ");
                GenProcName(N, MNonts);
                IO.WriteText(Mod, "(Ptr: HeapType);\n");
                IO.WriteText(Mod,
                        "BEGIN \n\tINC(OutputSize, ((Heap[Ptr] MOD refConst) DIV arityConst) + 1); \n");
                GenAlts(N);
                IO.WriteText(Mod, "END ");
                GenProcName(N, MNonts);
                IO.WriteText(Mod, ";\n\n");
            }
        }
    }

    EmitSpace = IO.IsOption("s");
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
    IO.WriteText(Mod, "\t\tIF IO.IsOption(\"i\") THEN \n");
    IO.WriteText(Mod, "\t\t\tIO.WriteText(IO.Msg, \"\\ttree of \"); ");
    IO.WriteText(Mod, "IO.WriteInt(IO.Msg, OutputSize); \n\t\t\t");
    IO.WriteString(Mod, "IO.WriteText(IO.Msg, \" uses \"); IO.WriteInt(IO.Msg, CountHeap()); ");
    IO.WriteText(Mod, "IO.WriteText(IO.Msg, \" of \"); \n\t\t\t");
    IO.WriteString(Mod,
            "IO.WriteInt(IO.Msg, NextHeap);  IO.WriteText(IO.Msg, \" allocated, with \"); ");
    IO.WriteText(Mod, "IO.WriteInt(IO.Msg, predefined + 1); \n\t\t\t");
    IO.WriteText(Mod, "IO.WriteText(IO.Msg, \" predefined\\n\"); IO.Update(IO.Msg); \n\t\tEND; \n");
}

void GenEmitCall(IO.TextOut Mod)
{
    IO.WriteText(Mod, "\t\t\tIF ");
    if (IO.IsOption("w"))
    {
        IO.WriteText(Mod, "~ ");
    }
    IO.WriteText(Mod, "IO.IsOption(\'w\') THEN IO.CreateOut(Out, \'");
    IO.WriteString(Mod, EAG.BaseName);
    IO.WriteText(Mod, ".Out\') ELSE Out := IO.Msg END; \n\t\t\t");
    IO.WriteString(Mod, "Emit");
    IO.WriteInt(Mod, StartMNont);
    IO.WriteString(Mod, "Type");
    if (Sets.In(Type2, StartMNont))
    {
        IO.Write(Mod, "2");
    }
    else
    {
        IO.Write(Mod, "3");
    }
    IO.WriteText(Mod, "(V1); IO.WriteLn(Out); IO.Show(Out); \n");
}

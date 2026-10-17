module epsilon.emitgen;

import epsilon.eag;
import epsilon.settings;
import runtime;
import std.bitmanip : BitArray;
import std.stdio : File;

private const CaseLabels = 127;
private BitArray Type3;
private BitArray Type2;
private int StartMNont;

public void GenEmitProc(File output, Settings settings)
{
    void CalcSets(int Nont)
    in (EAG.firstMNont <= Nont)
    in (Nont < eag.NextMNont)
    {
        int A;
        int F;
        int M;

        if (eag.MNont[Nont].IsToken)
            Type3[Nont] = true;
        A = eag.MNont[Nont].MRule;
        while (A != EAG.nil)
        {
            F = eag.MAlt[A].Right;
            while (eag.MembBuf[F] != EAG.nil)
            {
                M = eag.MembBuf[F];
                if (M > 0)
                {
                    if (Type3[Nont] && !Type3[M])
                    {
                        Type3[M] = true;
                        CalcSets(M);
                    }
                    if (Type2[Nont] && !Type2[M])
                    {
                        if (!eag.MNont[M].IsToken)
                            Type2[M] = true;
                        CalcSets(M);
                    }
                }
                ++F;
            }
            A = eag.MAlt[A].Next;
        }
    }

    void GenEmitProcs(BitArray MNonts)
    {
        void GenProcName(size_t N, BitArray Type)
        {
            output.write("Emit", N, "Type", (Type == Type2) ? "2" : "3");
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
                    output.write("Out.write(' '); ");
                else
                    output.write("Out.writeln; ");
            }

            A = eag.MNont[N].MRule;
            ANum = 1;
            output.writeln("switch (MOD(Heap[Ptr], arityConst))");
            output.writeln("{");
            while (A != EAG.nil)
            {
                if (ANum > CaseLabels)
                {
                    import std.stdio : stdout;  // TODO: replace with log

                    stdout.write("internal error: Too many meta alts in ");
                    stdout.write(eag.MTerm[N].Id.repr);
                    stdout.writeln;
                    assert(0);
                }
                F = eag.MAlt[A].Right;
                arity = 0;
                output.writeln("case ", ANum, ":");
                while (eag.MembBuf[F] != EAG.nil)
                {
                    M = eag.MembBuf[F];
                    if (M < 0)
                    {
                        output.write("Out.write(");
                        output.write(eag.MTerm[-M].Id.repr);
                        output.write("); ");
                        if (MNonts == Type2)
                            WhiteSpace;
                    }
                    else
                    {
                        if (MNonts == Type3 || eag.MNont[M].IsToken)
                            GenProcName(M, Type3);
                        else
                            GenProcName(M, Type2);
                        ++arity;
                        output.write("(Heap[Ptr + ");
                        output.write(arity);
                        output.write("]); ");
                        if (eag.MNont[M].IsToken && MNonts == Type2)
                            WhiteSpace;
                    }
                    ++F;
                    output.writeln;
                }
                output.writeln("break;");
                A = eag.MAlt[A].Next;
                ++ANum;
            }
            output.writeln("default:");
            output.writeln("Out.write(Heap[Ptr]);");
            output.writeln("}");
        }

        foreach (N; MNonts.bitsSet)
        {
            output.write("void ");
            GenProcName(N, MNonts);
            output.writeln("(HeapType Ptr)");
            output.writeln("{");
            output.writeln("OutputSize += DIV(MOD(Heap[Ptr], refConst), arityConst) + 1;");
            GenAlts(N);
            output.writeln("}");
            output.writeln;
        }
    }

    StartMNont = eag.DomBuf[eag.HNont[eag.StartSym].Sig];
    Type3 = BitArray();
    Type3.length = eag.NextMNont + 1;
    Type2 = BitArray();
    Type2.length = eag.NextMNont + 1;
    if (!eag.MNont[StartMNont].IsToken)
        Type2[StartMNont] = true;
    CalcSets(StartMNont);
    if (!Type3.bitsSet.empty)
        GenEmitProcs(Type3);
    if (!Type2.bitsSet.empty)
        GenEmitProcs(Type2);
}

public void GenShowHeap(File output) @safe
{
    output.writeln("if (info_)");
    output.writeln("{");
    output.write(`stdout.write("    tree of "); `);
    output.writeln("stdout.write(OutputSize);");
    output.writeln(`stdout.write(" uses ");`);
    output.writeln(`stdout.write(CountHeap());`);
    output.writeln(`stdout.write(" of ");`);
    output.writeln(`stdout.write(NextHeap);`);
    output.writeln(`stdout.write(" allocated, with ");`);
    output.writeln("stdout.write(predefined + 1);");
    output.writeln(`stdout.writeln(" predefined");`);
    output.writeln("}");
}

public void GenEmitCall(File output, Settings settings)
{
    output.write("if (");
    if (settings.write)
        output.write("!");
    output.writeln("write)");
    output.writeln(`Out = File("`, eag.BaseName, `.Out", "w");`);
    output.writeln("else");
    output.writeln("Out = stdout;");
    output.writeln("Emit", StartMNont, "Type",  Type2[StartMNont] ? "2" : "3", "(V1);");
    output.writeln("Out.writeln;");
    output.writeln("Out.flush;");
}

private string repr(int id)
{
    import std.format : format;
    import std.range : dropBackOne, dropOne, front, only;

    const value = eag.symbolTable.symbol(id);

    if (value.front == '\'')
    {
        if (value == `'"'`)
            return "`\"`";
        return format!`"%s"`(value.dropOne.dropBackOne);
    }
    return value;

}

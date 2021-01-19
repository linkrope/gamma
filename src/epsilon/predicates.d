module epsilon.predicates;

import EAG = epsilon.eag;
import IO = epsilon.io;
import runtime;
import std.bitmanip : BitArray;
import std.stdio;

void List()
{
    IO.Msg.write("Predicates in     ");
    IO.Msg.write(EAG.BaseName);
    IO.Msg.write(": ");
    if (EAG.Performed(EAG.analysed | EAG.predicates))
    {
        foreach (N; EAG.Pred.bitsSet)
        {
            writeln;
            writeln(EAG.HNont[N].Def.Sub.Pos);
            IO.Msg.write(" :  ");
            IO.Msg.write(EAG.HNontRepr(N));
        }
    }
    IO.Msg.writeln;
    IO.Msg.flush;
}

void Check()
{
    struct EdgeRecord
    {
        size_t Dest;
        int Next;
    }

    int[] HNont;
    EdgeRecord[] Edge;
    int NextEdge;
    size_t[] Stack;
    int Top;
    BitArray CoPred;
    BitArray Pred;

    void NewEdge(int From, size_t To)
    {
        Edge[NextEdge].Dest = To;
        Edge[NextEdge].Next = HNont[From];
        HNont[From] = NextEdge;
        ++NextEdge;
    }

    void PutCoPred(size_t N)
    {
        if (!CoPred[N])
        {
            CoPred[N] = true;
            Stack[Top] = N;
            ++Top;
        }
    }

    void BuiltEdge()
    {
        for (size_t N = EAG.firstHNont; N < EAG.NextHNont; ++N)
            HNont[N] = -1;
        foreach (N; EAG.All.bitsSet)
        {
            if (!EAG.Null[N])
                PutCoPred(N);

            EAG.Alt A = EAG.HNont[N].Def.Sub;

            do
            {
                EAG.Factor F = A.Sub;

                while (F !is null)
                {
                    if (cast(EAG.Term) F !is null)
                        PutCoPred(N);
                    else
                        NewEdge((cast(EAG.Nont) F).Sym, N);
                    F = F.Next;
                }
                A = A.Next;
            }
            while (A !is null);
        }
    }

    void ClearStack()
    {
        while (Top > 0)
        {
            --Top;

            int Dep = HNont[Stack[Top]];

            while (Dep >= 0)
            {
                PutCoPred(Edge[Dep].Dest);
                Dep = Edge[Dep].Next;
            }
        }
    }

    IO.Msg.write("Predicates in     ");
    IO.Msg.write(EAG.BaseName);
    IO.Msg.flush;
    if (EAG.Performed(EAG.analysed))
    {
        EAG.History &= ~EAG.predicates;
        HNont = new int[EAG.NextHNont];
        Edge = new  EdgeRecord[EAG.NONont + 1];
        NextEdge = 0;
        Stack = new size_t[EAG.NextHNont];
        Top = 0;
        CoPred = BitArray();
        CoPred.length = EAG.NextHNont + 1;
        BuiltEdge;
        ClearStack;
        Pred = EAG.Prod - CoPred;
        Pred[EAG.StartSym] = false;
        EAG.Pred = Pred;
        EAG.History |= EAG.predicates;

        const NOPreds = Pred.count;

        if (NOPreds > 0)
        {
            IO.Msg.write(":  ");
            IO.Msg.write(NOPreds);
            IO.Msg.write("      ePredicates.List ");
        }
        else
        {
            IO.Msg.write(":  none. ");
        }
    }
    IO.Msg.writeln;
    IO.Msg.flush;
}

module ePredicates;

import EAG = eEAG;
import IO = eIO;
import runtime;
import std.bitmanip : BitArray;
import std.stdio;

void List()
{
    int N;
    IO.Msg.write("Predicates in     ");
    IO.Msg.write(EAG.BaseName);
    IO.Msg.write(": ");
    if (EAG.Performed(EAG.analysed | EAG.predicates))
    {
        // TODO: foreach (N; EAG.Pred)
        for (N = EAG.firstHNont; N < EAG.NextHNont; ++N)
        {
            if (EAG.Pred[N])
            {
                writeln;
                writeln(EAG.HNont[N].Def.Sub.Pos);
                IO.Msg.write(" :  ");
                IO.Msg.write(EAG.HNontRepr(N));
            }
        }
    }
    IO.Msg.writeln;
    IO.Msg.flush;
}

void Check()
{
    struct EdgeRecord
    {
        int Dest;
        int Next;
    }

    int[] HNont;
    EdgeRecord[] Edge;
    int NextEdge;
    int[] Stack;
    int Top;
    BitArray CoPred;
    BitArray Pred;
    int NOPreds;
    int N;

    void NewEdge(int From, int To)
    {
        Edge[NextEdge].Dest = To;
        Edge[NextEdge].Next = HNont[From];
        HNont[From] = NextEdge;
        ++NextEdge;
    }

    void PutCoPred(int N)
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
        EAG.Alt A;
        EAG.Factor F;
        int N;

        for (N = EAG.firstHNont; N < EAG.NextHNont; ++N)
            HNont[N] = -1;
        // TODO: foreach (N; EAG.All)
        for (N = EAG.firstHNont; N < EAG.NextHNont; ++N)
        {
            if (EAG.All[N])
            {
                if (!EAG.Null[N])
                    PutCoPred(N);
                A = EAG.HNont[N].Def.Sub;
                do
                {
                    F = A.Sub;
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
    }

    void ClearStack()
    {
        int Dep;
        while (Top > 0)
        {
            --Top;
            Dep = HNont[Stack[Top]];
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
        Stack = new int[EAG.NextHNont];
        Top = 0;
        CoPred = BitArray();
        CoPred.length = EAG.NextHNont + 1;
        BuiltEdge;
        ClearStack;
        Pred = EAG.Prod - CoPred;
        Pred[EAG.StartSym] = false;
        EAG.Pred = Pred;
        EAG.History |= EAG.predicates;
        NOPreds = 0;
        // TODO: foreach (N; Pred)
        for (N = EAG.firstHNont; N <= EAG.NextHNont; ++N)
        {
            if (Pred[N])
                ++NOPreds;
        }
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

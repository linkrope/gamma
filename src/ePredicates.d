module ePredicates;

import EAG = eEAG;
import IO = eIO;
import runtime;
import Sets = set;
import std.stdio;

void List()
{
    int N;
    IO.Msg.write("Predicates in     ");
    IO.Msg.write(EAG.BaseName);
    IO.Msg.write(": ");
    if (EAG.Performed(Sets.SET(EAG.analysed, EAG.predicates)))
    {
        for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
        {
            if (Sets.In(EAG.Pred, N))
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
    Sets.OpenSet CoPred;
    Sets.OpenSet Pred;
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
        if (!Sets.In(CoPred, N))
        {
            Sets.Incl(CoPred, N);
            Stack[Top] = N;
            ++Top;
        }
    }

    void BuiltEdge()
    {
        EAG.Alt A;
        EAG.Factor F;
        int N;
        for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
        {
            HNont[N] = -1;
        }
        for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
        {
            if (Sets.In(EAG.All, N))
            {
                if (!Sets.In(EAG.Null, N))
                {
                    PutCoPred(N);
                }
                A = EAG.HNont[N].Def.Sub;
                do
                {
                    F = A.Sub;
                    while (F !is null)
                    {
                        if (cast(EAG.Term) F !is null)
                        {
                            PutCoPred(N);
                        }
                        else
                        {
                            NewEdge((cast(EAG.Nont) F).Sym, N);
                        }
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
    if (EAG.Performed(Sets.SET(EAG.analysed)))
    {
        Sets.EXCL(EAG.History, EAG.predicates);
        HNont = new int[EAG.NextHNont];
        Edge = new  EdgeRecord[EAG.NONont + 1];
        NextEdge = 0;
        Stack = new int[EAG.NextHNont];
        Top = 0;
        Sets.New(CoPred, EAG.NextHNont);
        Sets.New(Pred, EAG.NextHNont);
        BuiltEdge;
        ClearStack;
        Sets.Difference(Pred, EAG.Prod, CoPred);
        Sets.Excl(Pred, EAG.StartSym);
        EAG.Pred = Pred;
        Sets.INCL(EAG.History, EAG.predicates);
        NOPreds = 0;
        for (N = EAG.firstHNont; N <= EAG.NextHNont; ++N)
        {
            if (Sets.In(Pred, N))
            {
                ++NOPreds;
            }
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

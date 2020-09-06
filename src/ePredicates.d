module ePredicates;

import runtime;
import Sets = eSets;
import IO = eIO;
import EAG = eEAG;
import std.stdio;

void List()
{
    int N;
    IO.WriteString(IO.Msg, "Predicates in     ");
    IO.WriteString(IO.Msg, EAG.BaseName);
    IO.WriteText(IO.Msg, ": ");
    if (EAG.Performed(SET(EAG.analysed, EAG.predicates)))
    {
        for (N = EAG.firstHNont; N <= EAG.NextHNont - 1; ++N)
        {
            if (Sets.In(EAG.Pred, N))
            {
                writeln;
                writeln(EAG.HNont[N].Def.Sub.Pos);
                IO.WriteString(IO.Msg, " :  ");
                EAG.WriteHNont(IO.Msg, N);
            }
        }
    }
    IO.WriteLn(IO.Msg);
    IO.Update(IO.Msg);
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

    IO.WriteString(IO.Msg, "Predicates in     ");
    IO.WriteString(IO.Msg, EAG.BaseName);
    IO.Update(IO.Msg);
    if (EAG.Performed(SET(EAG.analysed)))
    {
        EXCL(EAG.History, EAG.predicates);
        NEW(HNont, EAG.NextHNont);
        NEW(Edge, EAG.NONont + 1);
        NextEdge = 0;
        NEW(Stack, EAG.NextHNont);
        Top = 0;
        Sets.New(CoPred, EAG.NextHNont);
        Sets.New(Pred, EAG.NextHNont);
        BuiltEdge;
        ClearStack;
        Sets.Difference(Pred, EAG.Prod, CoPred);
        Sets.Excl(Pred, EAG.StartSym);
        EAG.Pred = Pred;
        INCL(EAG.History, EAG.predicates);
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
            IO.WriteString(IO.Msg, ":  ");
            IO.WriteInt(IO.Msg, NOPreds);
            IO.WriteString(IO.Msg, "      ePredicates.List ");
        }
        else
        {
            IO.WriteString(IO.Msg, ":  none. ");
        }
    }
    IO.WriteLn(IO.Msg);
    IO.Update(IO.Msg);
}

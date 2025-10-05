module epsilon.predicates;

import EAG = epsilon.eag;
import log;
import runtime;
import std.bitmanip : BitArray;

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
                for (EAG.Factor F = A.Sub; F !is null; F = F.Next)
                    if (cast(EAG.Term) F)
                        PutCoPred(N);
                    else if (auto nont = cast(EAG.Nont) F)
                        NewEdge(nont.Sym, N);
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
    List;
}

private void List()
{
    import std.algorithm : map;
    import std.format : format;

    info!"predicates in %s: %s"(EAG.BaseName, EAG.Pred.count);
    if (EAG.Pred.count == 0)
        return;

    string[] items;

    foreach (N; EAG.Pred.bitsSet)
        if (EAG.HNont[N].anonymous)
            items ~= format!"EBNF expression in %s\n%s"(EAG.NamedHNontRepr(N), EAG.HNont[N].Def.Sub.Pos);
        else
            items ~= format!"%s\n%s"(EAG.HNontRepr(N), EAG.HNont[N].Def.Sub.Pos);

    trace!"predicate occurrences in %s:%-(\n%s%)"(EAG.BaseName, items);
}

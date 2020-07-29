module ePredicates;

import runtime;
import Sets = eSets;
import IO = eIO;
import Scanner = eScanner;
import EAG = eEAG;

void List()
{
    int Sym;
    IO.WriteString(IO.Msg, "Predicates in     ");
    IO.WriteString(IO.Msg, EAG.BaseName);
    IO.WriteText(IO.Msg, ": ");
    if (EAG.Performed(SET(1 << EAG.analysed | 1 << EAG.predicates)))
    {
        for (Sym = EAG.firstHNont; Sym <= EAG.NextHNont - 1; ++Sym)
        {
            if (Sets.In(EAG.Pred, Sym))
            {
                IO.WriteText(IO.Msg, "\n\t");
                IO.WritePos(IO.Msg, EAG.HNont[Sym].Def.Sub.Pos);
                IO.WriteString(IO.Msg, " :  ");
                EAG.WriteHNont(IO.Msg, Sym);
            }
        }
    }
    IO.WriteLn(IO.Msg);
    IO.Update(IO.Msg);
}

void Check()
{
    struct DependRecord
    {
        int Dest;
        int Next;
    }

    int[] HNont;
    DependRecord[] DependBuf;
    int NextDepend;
    int[] Stack;
    int Top;
    Sets.OpenSet Prod;
    Sets.OpenSet Pred;
    Sets.OpenSet Reach;
    int NOPreds;
    int Sym;

    void NewDepend(int From, int To)
    {
        DependBuf[NextDepend].Dest = To;
        DependBuf[NextDepend].Next = HNont[From];
        HNont[From] = NextDepend;
        ++NextDepend;
    }

    void PutProd(int Sym)
    {
        if (!Sets.In(Prod, Sym))
        {
            Sets.Incl(Prod, Sym);
            Stack[Top] = Sym;
            ++Top;
        }
    }

    void BuiltDependencies()
    {
        EAG.Alt A;
        EAG.Factor F;
        int Sym;
        for (Sym = EAG.firstHNont; Sym <= EAG.NextHNont - 1; ++Sym)
        {
            HNont[Sym] = -1;
        }
        for (Sym = EAG.firstHNont; Sym <= EAG.NextHNont - 1; ++Sym)
        {
            if (Sets.In(EAG.Prod, Sym))
            {
                A = EAG.HNont[Sym].Def.Sub;
                do
                {
                    F = A.Sub;
                    while (F !is null)
                    {
                        if (cast(EAG.Term) F !is null)
                        {
                            PutProd(Sym);
                        }
                        else
                        {
                            NewDepend((cast(EAG.Nont) F).Sym, Sym);
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
                PutProd(DependBuf[Dep].Dest);
                Dep = DependBuf[Dep].Next;
            }
        }
    }

    IO.WriteString(IO.Msg, "Predicates in     ");
    IO.WriteString(IO.Msg, EAG.BaseName);
    IO.Update(IO.Msg);
    if (EAG.Performed(SET(1 << EAG.analysed)))
    {
        EXCL(EAG.History, EAG.predicates);
        NEW(HNont, EAG.NextHNont);
        NEW(DependBuf, EAG.NONont + 1);
        NextDepend = 0;
        NEW(Stack, EAG.NextHNont);
        Top = 0;
        Sets.New(Prod, EAG.NextHNont);
        Sets.New(Pred, EAG.NextHNont);
        BuiltDependencies;
        ClearStack;
        Sets.Difference(Pred, EAG.Prod, Prod);
        Sets.Excl(Pred, EAG.StartSym);
        EAG.Pred = Pred;
        INCL(EAG.History, EAG.predicates);
        NOPreds = 0;
        for (Sym = EAG.firstHNont; Sym <= EAG.NextHNont; ++Sym)
        {
            if (Sets.In(Pred, Sym))
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

module eShift;

import runtime;
import Sets = eSets;
import IO = eIO;
import EAG = eEAG;
import io : UndefPos;

const nil = EAG.nil;

void Shift()
{
    int HN;
    int HT;
    EAG.Alt HA;
    EAG.Factor HF;
    int Rhs;
    int Num;
    int Var;
    Sets.OpenSet GenNonts;
    Sets.OpenSet Del;

    Sets.New(GenNonts, EAG.NextHNont);
    Sets.Difference(GenNonts, EAG.All, EAG.Pred);
    Sets.New(Del, EAG.NextHNont);
    Sets.Empty(Del);
    EAG.NextMAlt = EAG.firstMAlt;
    EAG.NextMemb = EAG.firstMemb;
    EAG.NextVar = EAG.firstVar;
    EAG.NextNode = EAG.firstNode;
    EAG.NextParam = EAG.firstParam;
    EAG.NextMTerm = EAG.NextHTerm - EAG.firstHTerm + EAG.firstMTerm;
    while (EAG.NextMTerm >= EAG.MTerm.length)
    {
        EAG.Expand;
    }
    for (HT = EAG.firstHTerm; HT <= EAG.NextHTerm - 1; ++HT)
    {
        EAG.MTerm[HT - EAG.firstHTerm + EAG.firstMTerm].Id = EAG.HTerm[HT].Id;
    }
    EAG.NextMNont = EAG.NextHNont - EAG.firstHNont + EAG.firstMNont;
    while (EAG.NextMNont >= EAG.MNont.length)
    {
        EAG.Expand;
    }
    for (HN = EAG.firstHNont; HN <= EAG.NextHNont - 1; ++HN)
    {
        if (Sets.In(GenNonts, HN))
        {
            EAG.MNont[HN - EAG.firstHNont + EAG.firstMNont].Id = EAG.HNont[HN].NamedId;
            EAG.MNont[HN - EAG.firstHNont + EAG.firstMNont].MRule = nil;
            EAG.MNont[HN - EAG.firstHNont + EAG.firstMNont].IsToken = EAG.HNont[HN].IsToken;
            HA = EAG.HNont[HN].Def.Sub;
            do
            {
                EAG.Scope = EAG.NextVar;
                HA.Scope.Beg = EAG.NextVar;
                HA.Formal.Pos = UndefPos;
                HA.Formal.Params = EAG.NextParam;
                EAG.AppParam(EAG.NextNode, UndefPos);
                EAG.ParamBuf[EAG.NextParam - 1].isDef = false;
                EAG.AppParam(nil, UndefPos);
                EAG.NodeBuf[EAG.NextNode] = EAG.NextMAlt;
                ++EAG.NextNode;
                if (EAG.NextNode >= EAG.NodeBuf.length)
                {
                    EAG.Expand;
                }
                Rhs = EAG.NextMemb;
                HF = HA.Sub;
                Num = 2;
                while (HF !is null)
                {
                    if (cast(EAG.Term) HF !is null)
                    {
                        EAG.AppMemb(-((cast(EAG.Term) HF).Sym - EAG.firstHTerm + EAG.firstMTerm));
                    }
                    else if (Sets.In(GenNonts, (cast(EAG.Nont) HF).Sym))
                    {
                        EAG.AppMemb((cast(EAG.Nont) HF).Sym - EAG.firstHNont + EAG.firstMNont);
                        Var = EAG.FindVar((cast(EAG.Nont) HF)
                                .Sym - EAG.firstHNont + EAG.firstMNont, Num, UndefPos, true);
                        EAG.NodeBuf[EAG.NextNode] = -Var;
                        ++EAG.NextNode;
                        if (EAG.NextNode >= EAG.NodeBuf.length)
                        {
                            EAG.Expand;
                        }
                        (cast(EAG.Nont) HF).Actual.Pos = UndefPos;
                        (cast(EAG.Nont) HF).Actual.Params = EAG.NextParam;
                        EAG.AppParam(-Var, UndefPos);
                        EAG.ParamBuf[EAG.NextParam - 1].isDef = true;
                        EAG.AppParam(nil, UndefPos);
                        ++Num;
                    }
                    else
                    {
                        if (HF.Next !is null)
                        {
                            HF.Next.Prev = HF.Prev;
                        }
                        if (HF.Prev !is null)
                        {
                            HF.Prev.Next = HF.Next;
                        }
                        if (HF == HA.Sub)
                        {
                            HA.Sub = HF.Next;
                        }
                        if (HF == HA.Last)
                        {
                            HA.Last = HF.Prev;
                        }
                    }
                    HF = HF.Next;
                }
                if (cast(EAG.Rep) EAG.HNont[HN].Def !is null)
                {
                    EAG.AppMemb(HN - EAG.firstHNont + EAG.firstMNont);
                    Var = EAG.FindVar(HN - EAG.firstHNont + EAG.firstMNont, Num, UndefPos, true);
                    EAG.NodeBuf[EAG.NextNode] = -Var;
                    ++EAG.NextNode;
                    if (EAG.NextNode >= EAG.NodeBuf.length)
                    {
                        EAG.Expand;
                    }
                    HA.Actual.Pos = UndefPos;
                    HA.Actual.Params = EAG.NextParam;
                    EAG.AppParam(-Var, UndefPos);
                    EAG.ParamBuf[EAG.NextParam - 1].isDef = true;
                    EAG.AppParam(nil, UndefPos);
                }
                EAG.AppMemb(nil);
                EAG.AppMemb(EAG.NewMAlt(HN - EAG.firstHNont + EAG.firstMNont, Rhs));
                HA.Scope.End = EAG.NextVar;
                HA = HA.Next;
            }
            while (HA !is null);
            if (cast(EAG.Opt) EAG.HNont[HN].Def !is null || cast(EAG.Rep) EAG.HNont[HN].Def !is null)
            {
                if (cast(EAG.Opt) EAG.HNont[HN].Def !is null)
                {
                    (cast(EAG.Opt) EAG.HNont[HN].Def).Formal.Pos = UndefPos;
                    (cast(EAG.Opt) EAG.HNont[HN].Def).Formal.Params = EAG.NextParam;
                    (cast(EAG.Opt) EAG.HNont[HN].Def).Scope.Beg = EAG.NextVar;
                    (cast(EAG.Opt) EAG.HNont[HN].Def).Scope.End = EAG.NextVar;
                }
                else
                {
                    (cast(EAG.Rep) EAG.HNont[HN].Def).Formal.Pos = UndefPos;
                    (cast(EAG.Rep) EAG.HNont[HN].Def).Formal.Params = EAG.NextParam;
                    (cast(EAG.Rep) EAG.HNont[HN].Def).Scope.Beg = EAG.NextVar;
                    (cast(EAG.Rep) EAG.HNont[HN].Def).Scope.End = EAG.NextVar;
                }
                EAG.AppParam(EAG.NextNode, UndefPos);
                EAG.ParamBuf[EAG.NextParam - 1].isDef = false;
                EAG.AppParam(nil, UndefPos);
                EAG.NodeBuf[EAG.NextNode] = EAG.NextMAlt;
                ++EAG.NextNode;
                if (EAG.NextNode >= EAG.NodeBuf.length)
                {
                    EAG.Expand;
                }
                Rhs = EAG.NextMemb;
                EAG.AppMemb(nil);
                EAG.AppMemb(EAG.NewMAlt(HN - EAG.firstHNont + EAG.firstMNont, Rhs));
            }
        }
        else
        {
            EAG.HNont[HN].Def = null;
            Sets.Incl(Del, HN);
            EAG.MNont[HN - EAG.firstHNont + EAG.firstMNont].Id = nil;
            EAG.MNont[HN - EAG.firstHNont + EAG.firstMNont].MRule = nil;
            EAG.MNont[HN - EAG.firstHNont + EAG.firstMNont].IsToken = false;
        }
    }
    EAG.NextDom = EAG.firstDom;
    for (HN = EAG.firstHNont; HN <= EAG.NextHNont - 1; ++HN)
    {
        if (Sets.In(GenNonts, HN))
        {
            EAG.HNont[HN].Sig = EAG.NextDom;
            EAG.AppDom('+', HN - EAG.firstHNont + EAG.firstMNont);
            EAG.AppDom('+', nil);
        }
    }
    Sets.Difference(EAG.All, EAG.All, Del);
    Sets.Difference(EAG.Pred, EAG.Pred, Del);
    Sets.Difference(EAG.Prod, EAG.Prod, Del);
    Sets.Difference(EAG.Reach, EAG.Reach, Del);
    Sets.Difference(EAG.Null, EAG.Null, Del);
}

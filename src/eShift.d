module eShift;

import runtime;
import Sets = eSets;
import IO = eIO;
import EAG = eEAG;

const nil = EAG.nil;

void Shift(int Dummy)
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
                HA.Formal.Pos = IO.UndefPos;
                HA.Formal.Params = EAG.NextParam;
                EAG.AppParam(EAG.NextNode, IO.UndefPos);
                EAG.ParamBuf[EAG.NextParam - 1].isDef = false;
                EAG.AppParam(nil, IO.UndefPos);
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
                    if (HF is EAG.Term)
                    {
                        EAG.AppMemb(-(HF(EAG.Term).Sym - EAG.firstHTerm + EAG.firstMTerm));
                    }
                    else if (Sets.In(GenNonts, HF(EAG.Nont).Sym))
                    {
                        EAG.AppMemb(HF(EAG.Nont).Sym - EAG.firstHNont + EAG.firstMNont);
                        Var = EAG.FindVar(HF(EAG.Nont)
                                .Sym - EAG.firstHNont + EAG.firstMNont, Num, IO.UndefPos, true);
                        EAG.NodeBuf[EAG.NextNode] = -Var;
                        ++EAG.NextNode;
                        if (EAG.NextNode >= EAG.NodeBuf.length)
                        {
                            EAG.Expand;
                        }
                        HF(EAG.Nont).Actual.Pos = IO.UndefPos;
                        HF(EAG.Nont).Actual.Params = EAG.NextParam;
                        EAG.AppParam(-Var, IO.UndefPos);
                        EAG.ParamBuf[EAG.NextParam - 1].isDef = true;
                        EAG.AppParam(nil, IO.UndefPos);
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
                if (EAG.HNont[HN].Def is EAG.Rep)
                {
                    EAG.AppMemb(HN - EAG.firstHNont + EAG.firstMNont);
                    Var = EAG.FindVar(HN - EAG.firstHNont + EAG.firstMNont, Num, IO.UndefPos, true);
                    EAG.NodeBuf[EAG.NextNode] = -Var;
                    ++EAG.NextNode;
                    if (EAG.NextNode >= EAG.NodeBuf.length)
                    {
                        EAG.Expand;
                    }
                    HA.Actual.Pos = IO.UndefPos;
                    HA.Actual.Params = EAG.NextParam;
                    EAG.AppParam(-Var, IO.UndefPos);
                    EAG.ParamBuf[EAG.NextParam - 1].isDef = true;
                    EAG.AppParam(nil, IO.UndefPos);
                }
                EAG.AppMemb(nil);
                EAG.AppMemb(EAG.NewMAlt(HN - EAG.firstHNont + EAG.firstMNont, Rhs));
                HA.Scope.End = EAG.NextVar;
                HA = HA.Next;
            }
            while (HA !is null);
            if (EAG.HNont[HN].Def is EAG.Opt || EAG.HNont[HN].Def is EAG.Rep)
            {
                if (EAG.HNont[HN].Def is EAG.Opt)
                {
                    EAG.HNont[HN].Def(EAG.Opt).Formal.Pos = IO.UndefPos;
                    EAG.HNont[HN].Def(EAG.Opt).Formal.Params = EAG.NextParam;
                    EAG.HNont[HN].Def(EAG.Opt).Scope.Beg = EAG.NextVar;
                    EAG.HNont[HN].Def(EAG.Opt).Scope.End = EAG.NextVar;
                }
                else
                {
                    EAG.HNont[HN].Def(EAG.Rep).Formal.Pos = IO.UndefPos;
                    EAG.HNont[HN].Def(EAG.Rep).Formal.Params = EAG.NextParam;
                    EAG.HNont[HN].Def(EAG.Rep).Scope.Beg = EAG.NextVar;
                    EAG.HNont[HN].Def(EAG.Rep).Scope.End = EAG.NextVar;
                }
                EAG.AppParam(EAG.NextNode, IO.UndefPos);
                EAG.ParamBuf[EAG.NextParam - 1].isDef = false;
                EAG.AppParam(nil, IO.UndefPos);
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
            EAG.AppDom("+", HN - EAG.firstHNont + EAG.firstMNont);
            EAG.AppDom("+", nil);
        }
    }
    Sets.Difference(EAG.All, EAG.All, Del);
    Sets.Difference(EAG.Pred, EAG.Pred, Del);
    Sets.Difference(EAG.Prod, EAG.Prod, Del);
    Sets.Difference(EAG.Reach, EAG.Reach, Del);
    Sets.Difference(EAG.Null, EAG.Null, Del);
}

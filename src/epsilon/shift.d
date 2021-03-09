module epsilon.shift;

import EAG = epsilon.eag;
import io : UndefPos;
import runtime;
import std.bitmanip : BitArray;
import std.conv : to;

private const nil = EAG.nil;

public void Shift()
{
    int HT;
    EAG.Alt HA;
    EAG.Factor HF;
    int Rhs;
    int Num;
    int Var;
    BitArray GenNonts = EAG.All - EAG.Pred;
    BitArray Del;

    Del.length = EAG.NextHNont + 1;
    EAG.NextMAlt = EAG.firstMAlt;
    EAG.NextMemb = EAG.firstMemb;
    EAG.NextVar = EAG.firstVar;
    EAG.NextNode = EAG.firstNode;
    EAG.NextParam = EAG.firstParam;
    EAG.NextMTerm = EAG.NextHTerm - EAG.firstHTerm + EAG.firstMTerm;
    while (EAG.NextMTerm >= EAG.MTerm.length)
        EAG.Expand;
    for (HT = EAG.firstHTerm; HT < EAG.NextHTerm; ++HT)
        EAG.MTerm[HT - EAG.firstHTerm + EAG.firstMTerm].Id = EAG.HTerm[HT].Id;
    EAG.NextMNont = EAG.NextHNont - EAG.firstHNont + EAG.firstMNont;
    while (EAG.NextMNont >= EAG.MNont.length)
        EAG.Expand;
    for (int HN = EAG.firstHNont; HN < EAG.NextHNont; ++HN)
    {
        if (GenNonts[HN])
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
                    EAG.Expand;
                Rhs = EAG.NextMemb;
                HF = HA.Sub;
                Num = 2;
                while (HF !is null)
                {
                    if (auto term = cast(EAG.Term) HF)
                    {
                        EAG.AppMemb(-(term.Sym - EAG.firstHTerm + EAG.firstMTerm));
                    }
                    else if (GenNonts[(cast(EAG.Nont) HF).Sym])
                    {
                        EAG.AppMemb((cast(EAG.Nont) HF).Sym - EAG.firstHNont + EAG.firstMNont);
                        Var = EAG.FindVar((cast(EAG.Nont) HF)
                                .Sym - EAG.firstHNont + EAG.firstMNont, Num, UndefPos, true);
                        EAG.NodeBuf[EAG.NextNode] = -Var;
                        ++EAG.NextNode;
                        if (EAG.NextNode >= EAG.NodeBuf.length)
                            EAG.Expand;
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
                            HF.Next.Prev = HF.Prev;
                        if (HF.Prev !is null)
                            HF.Prev.Next = HF.Next;
                        if (HF == HA.Sub)
                            HA.Sub = HF.Next;
                        if (HF == HA.Last)
                            HA.Last = HF.Prev;
                    }
                    HF = HF.Next;
                }
                if (cast(EAG.Rep) EAG.HNont[HN].Def)
                {
                    EAG.AppMemb(HN - EAG.firstHNont + EAG.firstMNont);
                    Var = EAG.FindVar(HN - EAG.firstHNont + EAG.firstMNont, Num, UndefPos, true);
                    EAG.NodeBuf[EAG.NextNode] = -Var;
                    ++EAG.NextNode;
                    if (EAG.NextNode >= EAG.NodeBuf.length)
                        EAG.Expand;
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
            if (cast(EAG.Opt) EAG.HNont[HN].Def || cast(EAG.Rep) EAG.HNont[HN].Def)
            {
                if (auto opt = cast(EAG.Opt) EAG.HNont[HN].Def)
                {
                    opt.Formal.Pos = UndefPos;
                    opt.Formal.Params = EAG.NextParam;
                    opt.Scope.Beg = EAG.NextVar;
                    opt.Scope.End = EAG.NextVar;
                }
                else if (auto rep = cast(EAG.Rep) EAG.HNont[HN].Def)
                {
                    rep.Formal.Pos = UndefPos;
                    rep.Formal.Params = EAG.NextParam;
                    rep.Scope.Beg = EAG.NextVar;
                    rep.Scope.End = EAG.NextVar;
                }
                EAG.AppParam(EAG.NextNode, UndefPos);
                EAG.ParamBuf[EAG.NextParam - 1].isDef = false;
                EAG.AppParam(nil, UndefPos);
                EAG.NodeBuf[EAG.NextNode] = EAG.NextMAlt;
                ++EAG.NextNode;
                if (EAG.NextNode >= EAG.NodeBuf.length)
                    EAG.Expand;
                Rhs = EAG.NextMemb;
                EAG.AppMemb(nil);
                EAG.AppMemb(EAG.NewMAlt(HN - EAG.firstHNont + EAG.firstMNont, Rhs));
            }
        }
        else
        {
            EAG.HNont[HN].Def = null;
            Del[HN] = true;
            EAG.MNont[HN - EAG.firstHNont + EAG.firstMNont].Id = nil;
            EAG.MNont[HN - EAG.firstHNont + EAG.firstMNont].MRule = nil;
            EAG.MNont[HN - EAG.firstHNont + EAG.firstMNont].IsToken = false;
        }
    }
    EAG.NextDom = EAG.firstDom;
    foreach (HN; GenNonts.bitsSet)
    {
        EAG.HNont[HN].Sig = EAG.NextDom;
        EAG.AppDom('+', HN.to!int - EAG.firstHNont + EAG.firstMNont);
        EAG.AppDom('+', nil);
    }
    EAG.All -= Del;
    EAG.Pred -= Del;
    EAG.Prod -= Del;
    EAG.Reach -= Del;
    EAG.Null -= Del;
}

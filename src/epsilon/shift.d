module epsilon.shift;

import epsilon.eag;
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
    BitArray GenNonts = eag.All - eag.Pred;
    BitArray Del;

    Del.length = eag.NextHNont + 1;
    eag.NextMAlt = EAG.firstMAlt;
    eag.MAlt.length = eag.NextMAlt;
    eag.NextMemb = EAG.firstMemb;
    eag.MembBuf.length = eag.NextMemb;
    eag.NextVar = EAG.firstVar;
    eag.Var.length = eag.NextVar;
    eag.NextNode = EAG.firstNode;
    eag.NodeBuf.length = eag.NextNode;
    eag.NextParam = EAG.firstParam;
    eag.ParamBuf.length = eag.NextParam;
    eag.NextMTerm = eag.NextHTerm - EAG.firstHTerm + EAG.firstMTerm;
    eag.MTerm.length = eag.NextMTerm;
    for (HT = EAG.firstHTerm; HT < eag.NextHTerm; ++HT)
        eag.MTerm[HT - EAG.firstHTerm + EAG.firstMTerm].Id = eag.HTerm[HT].Id;
    eag.NextMNont = eag.NextHNont - EAG.firstHNont + EAG.firstMNont;
    eag.MNont.length = eag.NextMNont;
    for (int HN = EAG.firstHNont; HN < eag.NextHNont; ++HN)
    {
        if (GenNonts[HN])
        {
            eag.MNont[HN - EAG.firstHNont + EAG.firstMNont].Id = eag.HNont[HN].NamedId;
            eag.MNont[HN - EAG.firstHNont + EAG.firstMNont].MRule = nil;
            eag.MNont[HN - EAG.firstHNont + EAG.firstMNont].IsToken = eag.HNont[HN].IsToken;
            HA = eag.HNont[HN].Def.Sub;
            do
            {
                eag.Scope = eag.NextVar;
                HA.Scope.Beg = eag.NextVar;
                HA.Formal.Pos = UndefPos;
                HA.Formal.Params = eag.NextParam;
                eag.AppParam(eag.NextNode, UndefPos);
                eag.ParamBuf[eag.NextParam - 1].isDef = false;
                eag.AppParam(nil, UndefPos);
                eag.AppNode(eag.NextMAlt);
                Rhs = eag.NextMemb;
                HF = HA.Sub;
                Num = 2;
                while (HF !is null)
                {
                    if (auto term = cast(EAG.Term) HF)
                    {
                        eag.AppMemb(-(term.Sym - EAG.firstHTerm + EAG.firstMTerm));
                    }
                    else if (GenNonts[(cast(EAG.Nont) HF).Sym])
                    {
                        eag.AppMemb((cast(EAG.Nont) HF).Sym - EAG.firstHNont + EAG.firstMNont);
                        Var = eag.FindVar((cast(EAG.Nont) HF)
                                .Sym - EAG.firstHNont + EAG.firstMNont, Num, UndefPos, true);
                        eag.AppNode(-Var);
                        (cast(EAG.Nont) HF).Actual.Pos = UndefPos;
                        (cast(EAG.Nont) HF).Actual.Params = eag.NextParam;
                        eag.AppParam(-Var, UndefPos);
                        eag.ParamBuf[eag.NextParam - 1].isDef = true;
                        eag.AppParam(nil, UndefPos);
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
                if (cast(EAG.Rep) eag.HNont[HN].Def)
                {
                    eag.AppMemb(HN - EAG.firstHNont + EAG.firstMNont);
                    Var = eag.FindVar(HN - EAG.firstHNont + EAG.firstMNont, Num, UndefPos, true);
                    eag.AppNode(-Var);
                    HA.Actual.Pos = UndefPos;
                    HA.Actual.Params = eag.NextParam;
                    eag.AppParam(-Var, UndefPos);
                    eag.ParamBuf[eag.NextParam - 1].isDef = true;
                    eag.AppParam(nil, UndefPos);
                }
                eag.AppMemb(nil);
                eag.AppMemb(eag.NewMAlt(HN - EAG.firstHNont + EAG.firstMNont, Rhs));
                HA.Scope.End = eag.NextVar;
                HA = HA.Next;
            }
            while (HA !is null);
            if (cast(EAG.Opt) eag.HNont[HN].Def || cast(EAG.Rep) eag.HNont[HN].Def)
            {
                if (auto opt = cast(EAG.Opt) eag.HNont[HN].Def)
                {
                    opt.Formal.Pos = UndefPos;
                    opt.Formal.Params = eag.NextParam;
                    opt.Scope.Beg = eag.NextVar;
                    opt.Scope.End = eag.NextVar;
                }
                else if (auto rep = cast(EAG.Rep) eag.HNont[HN].Def)
                {
                    rep.Formal.Pos = UndefPos;
                    rep.Formal.Params = eag.NextParam;
                    rep.Scope.Beg = eag.NextVar;
                    rep.Scope.End = eag.NextVar;
                }
                eag.AppParam(eag.NextNode, UndefPos);
                eag.ParamBuf[eag.NextParam - 1].isDef = false;
                eag.AppParam(nil, UndefPos);
                eag.AppNode(eag.NextMAlt);
                Rhs = eag.NextMemb;
                eag.AppMemb(nil);
                eag.AppMemb(eag.NewMAlt(HN - EAG.firstHNont + EAG.firstMNont, Rhs));
            }
        }
        else
        {
            eag.HNont[HN].Def = null;
            Del[HN] = true;
            eag.MNont[HN - EAG.firstHNont + EAG.firstMNont].Id = nil;
            eag.MNont[HN - EAG.firstHNont + EAG.firstMNont].MRule = nil;
            eag.MNont[HN - EAG.firstHNont + EAG.firstMNont].IsToken = false;
        }
    }
    eag.NextDom = EAG.firstDom;
    foreach (HN; GenNonts.bitsSet)
    {
        eag.HNont[HN].Sig = eag.NextDom;
        eag.AppDom('+', HN.to!int - EAG.firstHNont + EAG.firstMNont);
        eag.AppDom('+', nil);
    }
    eag.All -= Del;
    eag.Pred -= Del;
    eag.Prod -= Del;
    eag.Reach -= Del;
    eag.Null -= Del;
}

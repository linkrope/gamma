module eEarley;

import EAG = eEAG;
import io : Position;
import runtime;
import std.stdio;

const end = int.min;
const nil = EAG.nil;
const firstMSym = 1;
const firstItem = 1;

struct MSymRecord
{
    int Sym;
    int Num;
    Position Pos;
}

struct ItemRecord
{
    int Dot;
    int Back;
    int Left;
    int Sub;
}

MSymRecord[] MSymBuf;
int NextMSym;
ItemRecord[] ItemBuf;
int NextItem;
int CurList;
bool[] Predicted;

void Expand() nothrow @safe
{
    size_t NewLen(size_t ArrayLen)
    {
        if (ArrayLen <= DIV(size_t.max, 2))
        {
            return 2 * ArrayLen;
        }
        else
        {
            assert(0);
        }
    }

    if (NextMSym >= MSymBuf.length)
    {
        auto MSymBuf1 = new MSymRecord[NewLen(MSymBuf.length)];

        for (size_t i = firstMSym; i < MSymBuf.length; ++i)
        {
            MSymBuf1[i] = MSymBuf[i];
        }
        MSymBuf = MSymBuf1;
    }
    if (NextItem >= ItemBuf.length)
    {
        auto ItemBuf1 = new ItemRecord[NewLen(ItemBuf.length)];

        for (size_t i = firstItem; i < ItemBuf.length; ++i)
        {
            ItemBuf1[i] = ItemBuf[i];
        }
        ItemBuf = ItemBuf1;
    }
}

int StartAffixform() @nogc nothrow @safe
{
    return NextMSym;
}

void AppMSym(int Sym, int Num, Position Pos) nothrow @safe
{
    if (NextMSym >= MSymBuf.length)
    {
        Expand;
    }
    MSymBuf[NextMSym].Sym = Sym;
    MSymBuf[NextMSym].Num = Num;
    MSymBuf[NextMSym].Pos = Pos;
    ++NextMSym;
}

void EndAffixform(Position Pos) nothrow @safe
{
    AppMSym(end, 0, Pos);
}

void CopyAffixform(int From, ref int To) nothrow @safe
{
    To = NextMSym;
    while (true)
    {
        AppMSym(MSymBuf[From].Sym, MSymBuf[From].Num, MSymBuf[From].Pos);
        if (MSymBuf[From].Sym == end)
            break;
        else
            ++From;
    }
}

void Parse(int Dom, int Affixform, ref int Tree, bool Def) @safe
{
    void SimpleParse(int Dom, int Affixform, ref int Tree, bool Def)
    {
        int A;
        int m;
        int n;
        if (MSymBuf[Affixform].Sym == Dom && MSymBuf[Affixform + 1].Sym == end)
        {
            Tree = -EAG.FindVar(MSymBuf[Affixform].Sym, MSymBuf[Affixform].Num,
                    MSymBuf[Affixform].Pos, Def);
        }
        else
        {
            Tree = nil;
            A = EAG.MNont[Dom].MRule;
            do
            {
                m = EAG.MAlt[A].Right;
                n = Affixform;
                while (EAG.MembBuf[m] == MSymBuf[n].Sym)
                {
                    ++m;
                    ++n;
                }
                if (EAG.MembBuf[m] == 0 && MSymBuf[n].Sym == end)
                {
                    Tree = EAG.NextNode;
                    EAG.NodeBuf[EAG.NextNode] = A;
                    ++EAG.NextNode;
                    if (EAG.NextNode >= EAG.NodeBuf.length)
                    {
                        EAG.Expand;
                    }
                    n = Affixform;
                    while (MSymBuf[n].Sym != end)
                    {
                        if (MSymBuf[n].Sym > 0)
                        {
                            EAG.NodeBuf[EAG.NextNode] = -EAG.FindVar(MSymBuf[n].Sym,
                                    MSymBuf[n].Num, MSymBuf[n].Pos, Def);
                            ++EAG.NextNode;
                            if (EAG.NextNode >= EAG.NodeBuf.length)
                            {
                                EAG.Expand;
                            }
                        }
                        ++n;
                    }
                    return;
                }
                A = EAG.MAlt[A].Next;
            }
            while (!(A == nil));
        }
    }

    void EarleyParse(int Dom, int Affixform, ref int Tree, bool Def)
    {
        int PrevList;
        int CurSym;
        int i;
        void AddItem(int Dot, int Back, int Left, int Sub)
        {
            int I;
            if (EAG.MembBuf[Dot] >= 0 || EAG.MembBuf[Dot] == MSymBuf[CurSym + 1].Sym)
            {
                ItemBuf[NextItem].Dot = Dot;
                ItemBuf[NextItem].Back = Back;
                I = CurList;
                while (ItemBuf[I].Dot != Dot || ItemBuf[I].Back != Back)
                {
                    ++I;
                }
                if (I == NextItem)
                {
                    ItemBuf[NextItem].Left = Left;
                    ItemBuf[NextItem].Sub = Sub;
                    ++NextItem;
                    if (NextItem >= ItemBuf.length)
                    {
                        Expand;
                    }
                }
                ItemBuf[NextItem].Dot = nil;
            }
        }

        void Scanner()
        {
            int I;
            int Sub;
            if (MSymBuf[CurSym].Sym > 0)
            {
                Sub = -EAG.FindVar(MSymBuf[CurSym].Sym, MSymBuf[CurSym].Num,
                        MSymBuf[CurSym].Pos, Def);
            }
            else
            {
                Sub = nil;
            }
            I = PrevList;
            do
            {
                if (EAG.MembBuf[ItemBuf[I].Dot] == MSymBuf[CurSym].Sym)
                {
                    AddItem(ItemBuf[I].Dot + 1, ItemBuf[I].Back, I, Sub);
                }
                ++I;
            }
            while (!(ItemBuf[I].Dot == nil));
        }

        void Closure()
        {
            int I;
            int I1;
            int I2;
            int N;
            int A;
            bool Ready;
            do
            {
                I = CurList;
                Ready = true;
                do
                {
                    if (EAG.MembBuf[ItemBuf[I].Dot] > 0)
                    {
                        N = EAG.MembBuf[ItemBuf[I].Dot];
                        if (!Predicted[N])
                        {
                            A = EAG.MNont[N].MRule;
                            do
                            {
                                AddItem(EAG.MAlt[A].Right, CurList, nil, nil);
                                A = EAG.MAlt[A].Next;
                            }
                            while (!(A == nil));
                            Predicted[N] = true;
                        }
                    }
                    else if (EAG.MembBuf[ItemBuf[I].Dot] == 0)
                    {
                        N = EAG.MAlt[EAG.MembBuf[ItemBuf[I].Dot + 1]].Left;
                        I1 = ItemBuf[I].Back;
                        do
                        {
                            if (EAG.MembBuf[ItemBuf[I1].Dot] == N)
                            {
                                I2 = NextItem;
                                AddItem(ItemBuf[I1].Dot + 1, ItemBuf[I1].Back, I1, I);
                                if (I2 < NextItem && ItemBuf[I1].Back == CurList)
                                {
                                    Ready = false;
                                }
                            }
                            ++I1;
                        }
                        while (!(ItemBuf[I1].Dot == nil));
                    }
                    ++I;
                }
                while (!(I == NextItem));
            }
            while (!Ready);
        }

        void Init(int Start)
        {
            int i;

            if (Predicted is null || Predicted.length < EAG.NextMNont)
            {
                Predicted = new bool[EAG.NextMNont];
            }
            if (int.max - 3 >= EAG.NextMemb)
            {
                EAG.NextMemb += 3;
            }
            else
            {
                assert(0);
            }
            while (EAG.NextMemb >= EAG.MembBuf.length)
            {
                EAG.Expand;
            }
            EAG.NextMemb -= 3;
            EAG.MembBuf[EAG.NextMemb] = Start;
            EAG.MembBuf[EAG.NextMemb + 1] = end;
            EAG.MembBuf[EAG.NextMemb + 2] = 0;
            EAG.MembBuf[EAG.NextMemb + 3] = EAG.NextMAlt;
            EAG.MAlt[EAG.NextMAlt].Left = EAG.NextMNont;
            EAG.MAlt[EAG.NextMAlt].Right = EAG.NextMemb;
            NextItem = firstItem;
            CurList = NextItem;
            for (i = EAG.firstMNont; i < EAG.NextMNont; ++i)
                Predicted[i] = false;
            AddItem(EAG.NextMemb, CurList, nil, nil);
            Closure;
        }

        void CreateTree(int I, ref int Tree)
        {
            int SubTree;
            int A;
            A = EAG.MembBuf[ItemBuf[I].Dot + 1];
            EAG.NodeBuf[EAG.NextNode] = A;
            Tree = EAG.NextNode;
            if (int.max - EAG.MAlt[A].Arity - 1 >= EAG.NextNode)
                EAG.NextNode += EAG.MAlt[A].Arity + 1;
            else
                assert(0);
            while (EAG.NextNode >= EAG.NodeBuf.length)
                EAG.Expand;
            SubTree = EAG.NextNode - 1;
            do
            {
                if (ItemBuf[I].Sub > 0)
                {
                    CreateTree(ItemBuf[I].Sub, EAG.NodeBuf[SubTree]);
                    --SubTree;
                }
                else if (ItemBuf[I].Sub < 0)
                {
                    EAG.NodeBuf[SubTree] = ItemBuf[I].Sub;
                    --SubTree;
                }
                I = ItemBuf[I].Left;
            }
            while (I != nil);
        }

        CurSym = Affixform - 1;
        Init(Dom);
        do
        {
            PrevList = CurList;
            ++NextItem;
            CurList = NextItem;
            if (NextItem >= ItemBuf.length)
                Expand;
            for (i = EAG.firstMNont; i < EAG.NextMNont; ++i)
                Predicted[i] = false;
            ++CurSym;
            Scanner;
            if (CurList == NextItem)
            {
                import log : error;

                error!"%s affixform incorrect"(MSymBuf[CurSym].Pos);
                Tree = nil;
                return;
            }
            else
            {
                Closure;
            }
        }
        while (!(MSymBuf[CurSym].Sym == end));
        if (ItemBuf[ItemBuf[CurList].Left].Sub < 0)
        {
            Tree = ItemBuf[ItemBuf[CurList].Left].Sub;
        }
        else
        {
            CreateTree(ItemBuf[ItemBuf[CurList].Left].Sub, Tree);
        }
    }

    SimpleParse(Dom, Affixform, Tree, Def);
    if (Tree == nil)
    {
        EarleyParse(Dom, Affixform, Tree, Def);
    }
}

void Init() nothrow @safe
{
    MSymBuf = new MSymRecord[2047];
    NextMSym = firstMSym;
    ItemBuf = new ItemRecord[1023];
    NextItem = firstItem;
    Predicted = null;
}

void Finit() @nogc nothrow @safe
{
    MSymBuf = null;
    ItemBuf = null;
    Predicted = null;
}

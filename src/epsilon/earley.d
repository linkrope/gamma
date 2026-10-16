module epsilon.earley;

import epsilon.eag;
import io : Position;
import runtime;

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
        assert(ArrayLen <= DIV(size_t.max, 2));

        return 2 * ArrayLen;
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
    for (;;)
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
            Tree = -eag.FindVar(MSymBuf[Affixform].Sym, MSymBuf[Affixform].Num,
                    MSymBuf[Affixform].Pos, Def);
        }
        else
        {
            Tree = nil;
            A = eag.MNont[Dom].MRule;
            do
            {
                m = eag.MAlt[A].Right;
                n = Affixform;
                while (eag.MembBuf[m] == MSymBuf[n].Sym)
                {
                    ++m;
                    ++n;
                }
                if (eag.MembBuf[m] == 0 && MSymBuf[n].Sym == end)
                {
                    Tree = eag.NextNode;
                    eag.AppNode(A);
                    n = Affixform;
                    while (MSymBuf[n].Sym != end)
                    {
                        if (MSymBuf[n].Sym > 0)
                        {
                            eag.AppNode(-eag.FindVar(MSymBuf[n].Sym,
                                    MSymBuf[n].Num, MSymBuf[n].Pos, Def));
                        }
                        ++n;
                    }
                    return;
                }
                A = eag.MAlt[A].Next;
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
            if (eag.MembBuf[Dot] >= 0 || eag.MembBuf[Dot] == MSymBuf[CurSym + 1].Sym)
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
                Sub = -eag.FindVar(MSymBuf[CurSym].Sym, MSymBuf[CurSym].Num,
                        MSymBuf[CurSym].Pos, Def);
            }
            else
            {
                Sub = nil;
            }
            I = PrevList;
            do
            {
                if (eag.MembBuf[ItemBuf[I].Dot] == MSymBuf[CurSym].Sym)
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
                    if (eag.MembBuf[ItemBuf[I].Dot] > 0)
                    {
                        N = eag.MembBuf[ItemBuf[I].Dot];
                        if (!Predicted[N])
                        {
                            A = eag.MNont[N].MRule;
                            do
                            {
                                AddItem(eag.MAlt[A].Right, CurList, nil, nil);
                                A = eag.MAlt[A].Next;
                            }
                            while (!(A == nil));
                            Predicted[N] = true;
                        }
                    }
                    else if (eag.MembBuf[ItemBuf[I].Dot] == 0)
                    {
                        N = eag.MAlt[eag.MembBuf[ItemBuf[I].Dot + 1]].Left;
                        I1 = ItemBuf[I].Back;
                        do
                        {
                            if (eag.MembBuf[ItemBuf[I1].Dot] == N)
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

            if (Predicted is null || Predicted.length < eag.NextMNont)
            {
                Predicted = new bool[eag.NextMNont];
            }
            const right = eag.NextMemb;

            eag.MembBuf.length = eag.NextMemb;
            eag.MAlt.length = eag.NextMAlt;
            eag.MembBuf ~= Start;
            eag.MembBuf ~= end;
            eag.MembBuf ~= 0;
            eag.MembBuf ~= eag.NextMAlt;
            eag.MAlt ~= EAG.MAltRecord(eag.NextMNont, right, 0, nil);
            NextItem = firstItem;
            CurList = NextItem;
            for (i = EAG.firstMNont; i < eag.NextMNont; ++i)
                Predicted[i] = false;
            AddItem(eag.NextMemb, CurList, nil, nil);
            Closure;
        }

        void CreateTree(int I, ref int Tree)
        {
            int SubTree;
            int A;
            A = eag.MembBuf[ItemBuf[I].Dot + 1];
            Tree = eag.NextNode;
            eag.NodeBuf.length += eag.MAlt[A].Arity + 1;
            eag.NodeBuf[Tree] = A;
            eag.NextNode = cast(int) eag.NodeBuf.length;
            SubTree = eag.NextNode - 1;
            do
            {
                if (ItemBuf[I].Sub > 0)
                {
                    CreateTree(ItemBuf[I].Sub, eag.NodeBuf[SubTree]);
                    --SubTree;
                }
                else if (ItemBuf[I].Sub < 0)
                {
                    eag.NodeBuf[SubTree] = ItemBuf[I].Sub;
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
            for (i = EAG.firstMNont; i < eag.NextMNont; ++i)
                Predicted[i] = false;
            ++CurSym;
            Scanner;
            if (CurList == NextItem)
            {
                import log : error;

                error!"affixform incorrect\n%s"(MSymBuf[CurSym].Pos);
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

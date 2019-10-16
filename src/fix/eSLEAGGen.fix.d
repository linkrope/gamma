import runtime;

const errVal = 0;
const predefined = $;
const arityConst = $;
const undef = -1;
const initialHeapSize = 8192;
alias HeapType = $;
alias OpenHeap = $;
OpenHeap Heap;
HeapType NextHeap;
long OutputSize;
$
alias OpenPos = Eval.OpenPos;
OpenPos PosHeap;
OpenPos PosStack;
long PosTop;
$
const maxArity = $;
const refConst = $;
HeapType[maxArity] FreeList;
$ void EvalExpand()
{
    OpenHeap Heap1;
    long i;
    NEW(Heap1, 2 * Heap.length);
    for (i = 0; i <= Heap.length - 1; ++i)
    {
        Heap1[i] = Heap[i];
    }
    Heap = Heap1;
}

void Reset()
{
    Heap = null;
}

$ void EvalExpand()
{
    OpenHeap Heap1;
    OpenPos PosHeap1;
    long i;
    NEW(Heap1, 2 * Heap.length);
    NEW(PosHeap1, 2 * Heap.length);
    for (i = 0; i <= Heap.length - 1; ++i)
    {
        Heap1[i] = Heap[i];
        PosHeap1[i] = PosHeap[i];
    }
    Heap = Heap1;
    PosHeap = PosHeap1;
}

void Reset()
{
    Heap = null;
    PosHeap = null;
    Eval.Reset;
}

void PushPos()
{
    void PosExpand()
    {
        OpenPos PosStack1;
        long i;
        NEW(PosStack1, PosStack.length * 2);
        for (i = 0; i <= PosStack.length - 1; ++i)
        {
            PosStack1[i] = PosStack[i];
        }
        PosStack = PosStack1;
    }

    ++PosTop;
    if (PosTop == PosStack.length)
    {
        PosExpand;
    }
    PosStack[PosTop] = S.Pos;
}

void PopPos(HeapType Arity)
{
    long i;
    for (i = NextHeap + Arity; i <= NextHeap; i = i + -1)
    {
        PosHeap[i] = PosStack[PosTop];
        --PosTop;
    }
}

$ void GetHeap(HeapType Arity, ref HeapType Node)
{
    if (FreeList[Arity] == 0)
    {
        Node = NextHeap;
        if (NextHeap >= Heap.length - Arity - 1)
        {
            EvalExpand;
        }
        Heap[NextHeap] = 0;
        INC(NextHeap, Arity + 1);
    }
    else
    {
        Node = FreeList[Arity];
        FreeList[Arity] = Heap[FreeList[Arity]];
        Heap[Node] = 0;
    }
    ASSERT(DIV(Heap[Node], refConst) == 0, 95);
}

void FreeHeap(HeapType Node)
{
    long RArity;
    HeapType i;
    ASSERT(Node >= 0, 97);
    if (DIV(Heap[Node], refConst) <= 0)
    {
        RArity = DIV(MOD(Heap[Node], refConst), arityConst);
        for (i = Node + 1; i <= Node + RArity; ++i)
        {
            FreeHeap(Heap[i]);
        }
        ASSERT(DIV(Heap[Node], refConst) == 0, 96);
        ASSERT(Node > 0, 95);
        Heap[Node] = FreeList[RArity];
        FreeList[RArity] = Node;
    }
    else
    {
        DEC(Heap[Node], refConst);
    }
}

$ long CountHeap()
{
    long i;
    long HeapCells;
    HeapType Node;
    HeapCells = NextHeap;
    for (i = 0; i <= maxArity - 1; ++i)
    {
        Node = FreeList[i];
        while (Node != 0)
        {
            DEC(HeapCells, i + 1);
            Node = Heap[Node];
        }
    }
    return HeapCells;
}

long CountHeap()
{
    return NextHeap;
}

$ void SetErr()
{
    ++ErrorCounter;
    IO.WriteText(IO.Msg, "  ");
    IO.WritePos(IO.Msg, $Pos);
    IO.WriteText(IO.Msg, "  ");
}

void Error(char[] Msg)
{
    SetErr;
    IO.WriteText(IO.Msg, Msg);
    IO.WriteLn(IO.Msg);
    IO.Update(IO.Msg);
}

void PredError(char[] Msg)
{
    SetErr;
    IO.WriteText(IO.Msg, "predicate ");
    IO.WriteText(IO.Msg, Msg);
    IO.WriteText(IO.Msg, " failed");
    IO.WriteLn(IO.Msg);
    IO.Update(IO.Msg);
}

void AnalyseError(ref HeapType V, char[] Msg)
{
    if (V != errVal)
    {
        SetErr;
        IO.WriteText(IO.Msg, "analysis in '");
        IO.WriteText(IO.Msg, Msg);
        IO.WriteText(IO.Msg, "' failed");
        IO.WriteLn(IO.Msg);
        IO.Update(IO.Msg);
        $
        INC(Heap[errVal], refConst);
        FreeHeap(V);
        $
        V = errVal;
    }
}

bool Equal(HeapType Ptr1, HeapType Ptr2)
{
    long i;
    if (Ptr1 == Ptr2)
    {
        return true;
    }
    else if (MOD(Heap[Ptr1], refConst) == MOD(Heap[Ptr2], refConst))
    {
        for (i = 1; i <= DIV(MOD(Heap[Ptr1], refConst), arityConst); ++i)
        {
            if (!Equal(Heap[Ptr1 + i], Heap[Ptr2 + i]))
            {
                return false;
            }
        }
        return true;
    }
    return false;
}

void Eq(HeapType Ptr1, HeapType Ptr2, char[] ErrMsg)
{
    if (!Equal(Ptr1, Ptr2))
    {
        if (Ptr1 != errVal && Ptr2 != errVal)
        {
            Error(ErrMsg);
        }
    }
}

void UnEq(HeapType Ptr1, HeapType Ptr2, char[] ErrMsg)
{
    if (Equal(Ptr1, Ptr2))
    {
        if (Ptr1 != errVal && Ptr2 != errVal)
        {
            Error(ErrMsg);
        }
    }
}

bool EvalInitSucceeds()
{
    const magic = 1818326597;
    const name = "$";
    const tabTimeStamp = $;
    IO.File Tab;
    bool OpenError;
    int i;
    long l;
    void LoadError(char[] Msg)
    {
        IO.WriteText(IO.Msg, "  loading the evaluator table ");
        IO.WriteString(IO.Msg, name);
        IO.WriteText(IO.Msg, " failed\n\t");
        IO.WriteText(IO.Msg, Msg);
        IO.WriteLn(IO.Msg);
        IO.Update(IO.Msg);
    }

    IO.OpenFile(Tab, name, OpenError);
    if (OpenError)
    {
        LoadError("it could not be opened");
        return false;
    }
    IO.GetLInt(Tab, l);
    if (l != magic)
    {
        LoadError("not an evaluator table");
        return false;
    }
    IO.GetLInt(Tab, l);
    if (l != tabTimeStamp)
    {
        LoadError("wrong time stamp");
        return false;
    }
    IO.GetLInt(Tab, l);
    if (l != predefined)
    {
        LoadError("wrong heap size");
        return false;
    }
    if (Heap == null)
    {
        NEW(Heap, initialHeapSize);
    }
    while (predefined >= Heap.length)
    {
        EvalExpand;
    }
    for (i = 0; i <= predefined; ++i)
    {
        IO.GetLInt(Tab, l);
        Heap[i] = l;
    }
    IO.GetLInt(Tab, l);
    if (l != tabTimeStamp)
    {
        LoadError("file corrupt");
        return false;
    }
    IO.CloseFile(Tab);
    for (i = 0; i <= maxArity - 1; ++i)
    {
        FreeList[i] = 0;
    }
    NextHeap = predefined + 1;
    OutputSize = 0;
    $
    PosTop = -1;
    NEW(PosStack, 128);
    if (PosHeap == null)
    {
        NEW(PosHeap, Heap.length);
    }
    $
    return true;
}

$

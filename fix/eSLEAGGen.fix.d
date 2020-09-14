// eSLEAGGen.Fix Version 1.03 --  dk 20.11.97

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
    OpenHeap Heap1 = new HeapType[2 * Heap.length];

    for (size_t i = 0; i <= Heap.length - 1; ++i)
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
    OpenHeap Heap1 = new HeapType[2 * Heap.length];
    OpenPos PosHeap1 = new Position[2 * Heap.length];

    for (size_t i = 0; i <= Heap.length - 1; ++i)
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
        OpenPos PosStack1 = new Position[PosStack.length * 2];

        for (size_t i = 0; i <= PosStack.length - 1; ++i)
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
    for (size_t i = NextHeap + Arity; i >= NextHeap; --i)
    {
        PosHeap[i] = PosStack[PosTop];
        --PosTop;
    }
}
$
void GetHeap(HeapType Arity, ref HeapType Node)
out (; DIV(Heap[Node], refConst) == 0)
{
    if (FreeList[Arity] == 0)
    {
        Node = NextHeap;
        if (NextHeap >= Heap.length - Arity - 1)
        {
            EvalExpand;
        }
        Heap[NextHeap] = 0;
        NextHeap += Arity + 1;
    }
    else
    {
        Node = FreeList[Arity];
        FreeList[Arity] = Heap[FreeList[Arity]];
        Heap[Node] = 0;
    }
}

void FreeHeap(HeapType Node)
in (Node >= 0)
{
    long RArity;
    HeapType i;

    if (DIV(Heap[Node], refConst) <= 0)
    {
        RArity = DIV(MOD(Heap[Node], refConst), arityConst);
        for (i = Node + 1; i <= Node + RArity; ++i)
        {
            FreeHeap(Heap[i]);
        }

        assert(DIV(Heap[Node], refConst) == 0);
        assert(Node > 0);

        Heap[Node] = FreeList[RArity];
        FreeList[RArity] = Node;
    }
    else
    {
        Heap[Node] -= refConst;
    }
}

long CountHeap()
{
    long HeapCells = NextHeap;
    HeapType Node;

    for (size_t i = 0; i <= maxArity - 1; ++i)
    {
        Node = FreeList[i];
        while (Node != 0)
        {
            HeapCells -= i + 1;
            Node = Heap[Node];
        }
    }
    return HeapCells;
}

$ long CountHeap()
{
    return NextHeap;
}

$ void SetErr()
{
    ++ErrorCounter;
    writeln;
    writeln($Pos);
}

void Error(string Msg)
{
    SetErr;
    IO.Msg.write(Msg);
    IO.Msg.writeln;
    IO.Msg.flush;
}

void PredError(string Msg)
{
    SetErr;
    IO.Msg.write("predicate ");
    IO.Msg.write(Msg);
    IO.Msg.write(" failed");
    IO.Msg.writeln;
    IO.Msg.flush;
}

void AnalyseError(ref HeapType V, string Msg)
{
    if (V != errVal)
    {
        SetErr;
        IO.Msg.write("analysis in '");
        IO.Msg.write(Msg);
        IO.Msg.write("' failed");
        IO.Msg.writeln;
        IO.Msg.flush;
        $
        Heap[errVal] += refConst;
        FreeHeap(V);
        $
        V = errVal;
    }
}

bool Equal(HeapType Ptr1, HeapType Ptr2)
{
    if (Ptr1 == Ptr2)
    {
        return true;
    }
    else if (MOD(Heap[Ptr1], refConst) == MOD(Heap[Ptr2], refConst))
    {
        for (size_t i = 1; i <= DIV(MOD(Heap[Ptr1], refConst), arityConst); ++i)
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

void Eq(HeapType Ptr1, HeapType Ptr2, string ErrMsg)
{
    if (!Equal(Ptr1, Ptr2))
    {
        if (Ptr1 != errVal && Ptr2 != errVal)
        {
            Error(ErrMsg);
        }
    }
}

void UnEq(HeapType Ptr1, HeapType Ptr2, string ErrMsg)
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
    const magic = 1_818_326_597;
    const name = "$";
    const tabTimeStamp = $;
    IO.File Tab;
    bool OpenError;
    long l;

    void LoadError(string Msg)
    {
        IO.Msg.write("  loading the evaluator table ");
        IO.Msg.write(name);
        IO.Msg.write(" failed\n\t");
        IO.Msg.write(Msg);
        IO.Msg.writeln;
        IO.Msg.flush;
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
    if (Heap is null)
    {
        Heap = new HeapType[initialHeapSize];
    }
    while (predefined >= Heap.length)
    {
        EvalExpand;
    }
    for (size_t i = 0; i <= predefined; ++i)
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
    for (size_t i = 0; i <= maxArity - 1; ++i)
    {
        FreeList[i] = 0;
    }
    NextHeap = predefined + 1;
    OutputSize = 0;
    $
    PosTop = -1;
    PosStack = new Position[128];
    if (PosHeap is null)
    {
        PosHeap = new Position[Heap.length];
    }
    $
    return true;
}

// eSLEAGGen.Fix end
$

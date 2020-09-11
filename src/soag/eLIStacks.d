module soag.eLIStacks;

import runtime;

const emptyStack = -1;
const firstStackElem = 0;
alias DataType = long;
alias StackList = DataType[];

struct Stack
{
    int Top;
    StackList Elem;
}

void Expand(ref Stack S)
{
    StackList List1;

    if (S.Elem.length < DIV(int.max, 2))
    {
        List1 = new DataType[2 * S.Elem.length + 1];
    }
    else
    {
        assert(0);
    }
    for (size_t i = firstStackElem; i <= S.Top; ++i)
    {
        List1[i] = S.Elem[i];
    }
    S.Elem = List1;
}

void New(ref Stack S, int Len)
{
    S = Stack();
    S.Elem = new DataType[Len];
    S.Top = emptyStack;
}

void Reset(ref Stack S)
{
    S.Top = emptyStack;
}

void Push(ref Stack S, DataType Val)
{
    if (S.Top + 2 >= S.Elem.length)
        Expand(S);

    ++S.Top;
    S.Elem[S.Top] = Val;
}

void Pop(ref Stack S)
{
    --S.Top;
}

DataType Top(ref Stack S)
{
    return S.Elem[S.Top];
}

DataType TopPop(ref Stack S)
{
    DataType R;
    R = S.Elem[S.Top];
    --S.Top;
    return R;
}

bool IsEmpty(Stack S)
{
    return S.Top <= emptyStack;
}

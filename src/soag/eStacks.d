module soag.eStacks;

import runtime;
import ALists = soag.eALists;
import IO = eIO;

struct Stack
{
    alias aList this;

    ALists.AListDesc aList;
}

void New(ref Stack S, int Len)
{
    ALists.New(S.aList, Len);
}

void Reset(ref Stack S)
{
    ALists.Reset(S.aList);
}

void Push(ref Stack S, int Val)
{
    ALists.Append(S.aList, Val);
}

void Pop(ref Stack S, ref int Val)
{
    Val = S.Elem[S.Last];
    ALists.Delete(S.aList, S.Last);
}

int Top(ref Stack S)
{
    return S.Elem[S.Last];
}

bool IsEmpty(Stack S)
{
    return S.Last < ALists.firstIndex;
}

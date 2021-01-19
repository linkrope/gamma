module epsilon.soag.stacks;

import runtime;
import ALists = epsilon.soag.alists;

struct Stack
{
    ALists.AListDesc aList;
}

void New(ref Stack S, int Len) nothrow pure @safe
{
    S = Stack();
    ALists.New(S.aList, Len);
}

@("create new empty stack")
unittest
{
    Stack stack;

    New(stack, 0);
    assert(IsEmpty(stack));
}

void Reset(ref Stack S) @nogc nothrow pure @safe
{
    ALists.Reset(S.aList);
}

@("reset stack")
unittest
{
    Stack stack;

    New(stack, 0);
    Push(stack, 3);
    Reset(stack);
    assert(IsEmpty(stack));
}

void Push(ref Stack S, int Val) nothrow pure @safe
{
    ALists.Append(S.aList, Val);
}

@("push value on stack")
unittest
{
    Stack stack;

    New(stack, 0);
    Push(stack, 3);
    assert(!IsEmpty(stack));
    assert(Top(stack) == 3);
}

void Pop(ref Stack S, ref int Val) @nogc nothrow
in (!IsEmpty(S))
{
    Val = S.aList.Elem[S.aList.Last];
    ALists.Delete(S.aList, S.aList.Last);
}

@("pop value from non-empty stack")
unittest
{
    Stack stack;
    int value;

    New(stack, 0);
    Push(stack, 3);
    Pop(stack, value);
    assert(value == 3);
    assert(IsEmpty(stack));
}

int Top(ref Stack S) @nogc nothrow
in (!IsEmpty(S))
{
    return S.aList.Elem[S.aList.Last];
}

bool IsEmpty(Stack S) @nogc nothrow
{
    return S.aList.Last < ALists.firstIndex;
}

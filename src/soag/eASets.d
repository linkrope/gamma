module soag.eASets;

import runtime;
import ALists = soag.eALists;

const firstIndex = ALists.firstIndex;
const noelem = -1;

struct ASetDesc
{
    int Max;
    ALists.AList List;
}

alias ASet = ASetDesc;

ASet S;

void New(ref ASet S, int MaxElem)
{
    S = ASet();
    ALists.New(S.List, MaxElem + 1);
    S.Max = MaxElem;
    for (int i = firstIndex; i <= MaxElem; ++i)
        S.List.Elem[i] = noelem;
}

@("create new empty set")
unittest
{
    ASet set;

    New(set, 1);

    assert(set.IsEmpty);
    assert(!In(set, 0));
    assert(!In(set, 1));
}

void Reset(ref ASet S)
{
    ALists.Reset(S.List);
    for (int i = firstIndex; i <= S.Max; ++i)
        S.List.Elem[i] = noelem;
}

@("reset set")
unittest
{
    ASet set;

    New(set, 1);
    Insert(set, 0);
    Insert(set, 1);
    Reset(set);

    assert(set.IsEmpty);
    assert(!In(set, 0));
    assert(!In(set, 1));
}

void Insert(ref ASet S, int Elem)
in (Elem <= S.Max)
{
    if (Elem <= S.List.Last)
    {
        if (S.List.Elem[Elem] == Elem)
        {
            // element already in set
        }
        else
        {
            ++S.List.Last;
            if (S.List.Elem[S.List.Last] > noelem)
            {
                S.List.Elem[S.List.Elem[S.List.Last]] = S.List.Elem[Elem];
                S.List.Elem[S.List.Elem[Elem]] = S.List.Elem[S.List.Last];
                S.List.Elem[S.List.Last] = S.List.Last;
            }
            else
            {
                S.List.Elem[S.List.Last] = S.List.Elem[Elem];
                S.List.Elem[S.List.Elem[Elem]] = S.List.Last;
            }
            S.List.Elem[Elem] = Elem;
        }
    }
    else
    {
        if (S.List.Elem[Elem] > noelem)
        {
            // element already in set
        }
        else
        {
            ++S.List.Last;
            if (S.List.Elem[S.List.Last] > noelem)
            {
                S.List.Elem[S.List.Elem[S.List.Last]] = Elem;
                S.List.Elem[Elem] = S.List.Elem[S.List.Last];
                S.List.Elem[S.List.Last] = S.List.Last;
            }
            else
            {
                S.List.Elem[S.List.Last] = Elem;
                S.List.Elem[Elem] = S.List.Last;
            }
        }
    }
}

@("insert element in set")
unittest
{
    ASet set;

    New(set, 1);
    Insert(set, 1);

    assert(!set.IsEmpty);
    assert(!In(set, 0));
    assert(In(set, 1));
}

void Delete(ref ASet S, int Elem)
in (Elem <= S.Max)
{
    const last = S.List.Last;

    if (Elem <= last)
    {
        if (S.List.Elem[Elem] == Elem)
        {
            if (Elem == last)
            {
                S.List.Elem[last] = noelem;
            }
            else
            {
                if (S.List.Elem[last] == last)
                {
                    S.List.Elem[Elem] = last;
                    S.List.Elem[last] = Elem;
                }
                else
                {
                    S.List.Elem[Elem] = S.List.Elem[last];
                    S.List.Elem[S.List.Elem[last]] = Elem;
                    S.List.Elem[last] = noelem;
                }
            }
            --S.List.Last;
        }
        else
        {
            // element already not set
        }
    }
    else if (Elem > last)
    {
        if (S.List.Elem[Elem] > noelem)
        {
            if (S.List.Elem[last] == last)
            {
                S.List.Elem[S.List.Elem[Elem]] = last;
                S.List.Elem[last] = S.List.Elem[Elem];
            }
            else
            {
                S.List.Elem[S.List.Elem[Elem]] = S.List.Elem[last];
                S.List.Elem[S.List.Elem[last]] = S.List.Elem[Elem];
                S.List.Elem[last] = noelem;
            }
            S.List.Elem[Elem] = noelem;
            --S.List.Last;
        }
        else
        {
            // element already not in set
        }
    }
    else
        assert(0);
}

@("remove element in set")
unittest
{
    ASet set;

    New(set, 1);
    Insert(set, 0);
    Insert(set, 1);
    Delete(set, 1);

    assert(!set.IsEmpty);
    assert(In(set, 0));
    assert(!In(set, 1));
}

bool IsEmpty(const ASet S)
{
    return S.List.Last < firstIndex;
}

bool In(ASet S, int Elem)
{
    return (Elem > S.List.Last) ? S.List.Elem[Elem] > noelem : S.List.Elem[Elem] == Elem;
}

int[] elements(ASet S)
{
    return S.List.Elem[firstIndex .. S.List.Last + 1];
}

@("regression test for issue in single-sweep computation")
unittest
{
    {
        ASet set;

        New(set, 3);
        Insert(set, 0);
        Insert(set, 2);
        Delete(set, 2);
        Delete(set, 0);

        assert(IsEmpty(set));

        Insert(set, 0);

        assert(!IsEmpty(set));
    }
    {
        ASet set;

        New(set, 3);
        Insert(set, 0);
        Insert(set, 2);
        // same as above, but deleted in different order
        Delete(set, 0);
        Delete(set, 2);

        assert(IsEmpty(set));

        Insert(set, 0);

        assert(!IsEmpty(set));
    }
}

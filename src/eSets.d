module eSets;

import runtime;

const M = 31 + 1;
alias OpenSet = uint[];

void New(ref OpenSet s0, int MaxElem)
{
    int n;
    NEW(s0, DIV(MaxElem, M) + 1);
    for (n = 0; n <= DIV(MaxElem, M); ++n)
    {
        s0[n] = SET;
    }
}

///
unittest
{
    OpenSet set;

    New(set, 32);

    assert(set == [0, 0]);
}

void Empty(ref OpenSet s0)
{
    int n;
    for (n = 0; n <= SHORT(s0.length - 1); ++n)
    {
        s0[n] = SET;
    }
}

///
unittest
{
    OpenSet set = [1234, 5678];

    Empty(set);

    assert(set == [0, 0]);
}

void Incl(ref OpenSet s0, int n)
{
    INCL(s0[DIV(n, M)], MOD(n, M));
}


///
unittest
{
    OpenSet set = [1, 0];

    Incl(set, 32);

    assert(set == [1, 1]);
}

void Excl(ref OpenSet s0, int n)
{
    EXCL(s0[DIV(n, M)], MOD(n, M));
}

///
unittest
{
    OpenSet set = [1, 1];

    Excl(set, 32);

    assert(set == [1, 0]);
}

void Assign(ref OpenSet s0, OpenSet s1)
{
    int n;
    for (n = 0; n <= SHORT(s1.length) - 1; ++n)
    {
        s0[n] = s1[n];
    }
}

///
unittest
{
    OpenSet set = [1234, 5678];

    Assign(set, [1, 1]);

    assert(set == [1, 1]);
}

void Complement(ref OpenSet s0, OpenSet s1)
{
    int n;
    for (n = 0; n <= SHORT(s1.length) - 1; ++n)
    {
        s0[n] = ~s1[n];
    }
}

///
unittest
{
    OpenSet set = [1234, 5678];

    Complement(set, [0, 0]);

    assert(set == [0xffffffff, 0xffffffff]);
}

void Union(ref OpenSet s0, OpenSet s1, OpenSet s2)
{
    int n;
    uint s;
    for (n = 0; n <= SHORT(s1.length) - 1; ++n)
    {
        s = s1[n] | s2[n];
        s0[n] = s;
    }
}

///
unittest
{
    OpenSet set = [1234, 5678];

    Union(set, [0b1010, 0b0101], [0b0011, 0b1100]);

    assert(set == [0b1011, 0b1101]);
}

void Difference(ref OpenSet s0, OpenSet s1, OpenSet s2)
{
    int n;
    uint s;
    for (n = 0; n <= SHORT(s1.length) - 1; ++n)
    {
        s = s1[n] & ~s2[n];
        s0[n] = s;
    }
}

///
unittest
{
    OpenSet set = [1234, 5678];

    Difference(set, [0b1010, 0b0101], [0b0011, 0b1100]);

    assert(set == [0b1000, 0b0001]);
}

void Intersection(ref OpenSet s0, OpenSet s1, OpenSet s2)
{
    int n;
    uint s;
    for (n = 0; n <= SHORT(s1.length) - 1; ++n)
    {
        s = s1[n] & s2[n];
        s0[n] = s;
    }
}

///
unittest
{
    OpenSet set = [1234, 5678];

    Intersection(set, [0b1010, 0b0101], [0b0011, 0b1100]);

    assert(set == [0b0010, 0b0100]);
}

void SymmetricDifference(ref OpenSet s0, OpenSet s1, OpenSet s2)
{
    int n;
    uint s;
    for (n = 0; n <= SHORT(s1.length) - 1; ++n)
    {
        s = s1[n] ^ s2[n];
        s0[n] = s;
    }
}

///
unittest
{
    OpenSet set = [1234, 5678];

    SymmetricDifference(set, [0b1010, 0b0101], [0b0011, 0b1100]);

    assert(set == [0b1001, 0b1001]);
}

bool In(OpenSet s1, int n)
{
    return IN(s1[DIV(n, M)], MOD(n, M));
}

///
unittest
{
    assert(In([1, 1], 32));
    assert(!In([1, 1], 1));
}

bool Included(OpenSet s1, OpenSet s2)
{
    int n;
    for (n = 0; n <= SHORT(s2.length) - 1; ++n)
    {
        if ((s1[n] | s2[n]) != s1[n])
        {
            return false;
        }
    }
    return true;
}

///
unittest
{
    assert(Included([0b1010, 0b0101], [0b1000, 0b0001]));
    assert(!Included([0b1000, 0b0001], [0b1010, 0b0101]));
}

bool IsEmpty(OpenSet s1)
{
    int n;
    for (n = 0; n <= SHORT(s1.length) - 1; ++n)
    {
        if (s1[n] != SET)
        {
            return false;
        }
    }
    return true;
}

///
unittest
{
    assert(IsEmpty([0, 0]));
    assert(!IsEmpty([0, 1]));
}

bool Equal(OpenSet s1, OpenSet s2)
{
    int n;
    for (n = 0; n <= SHORT(s1.length) - 1; ++n)
    {
        if (s1[n] != s2[n])
        {
            return false;
        }
    }
    return true;
}

///
unittest
{
    assert(Equal([0, 1], [0, 1]));
    assert(!Equal([0, 0], [0, 1]));
}

bool Disjoint(OpenSet s1, OpenSet s2)
{
    int n;
    for (n = 0; n <= SHORT(s1.length) - 1; ++n)
    {
        if ((s1[n] & s2[n]) != SET)
        {
            return false;
        }
    }
    return true;
}

///
unittest
{
    assert(Disjoint([0b1010, 0b0101], [0b0001, 0b1000]));
    assert(!Disjoint([0b1010, 0b0101], [0b0001, 0b0100]));
}

int nSetsUsed(OpenSet s1)
{
    return SHORT(s1.length);
}

///
unittest
{
    assert(nSetsUsed([1234, 5678]) == 2);
}

uint ConvertToSET(OpenSet s1, int Index)
{
    return s1[Index];
}

///
unittest
{
    assert(ConvertToSET([1234, 5678], 1) == 5678);
}

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
        s0[n] = Set;
    }
}

void Empty(ref OpenSet s0)
{
    int n;
    for (n = 0; n <= SHORT(s0.length - 1); ++n)
    {
        s0[n] = Set;
    }
}

void Incl(ref OpenSet s0, int n)
{
    INCL(s0[DIV(n, M)], MOD(n, M));
}

void Excl(ref OpenSet s0, int n)
{
    EXCL(s0[DIV(n, M)], MOD(n, M));
}

void Assign(ref OpenSet s0, OpenSet s1)
{
    int n;
    for (n = 0; n <= SHORT(s1.length) - 1; ++n)
    {
        s0[n] = s1[n];
    }
}

void Complement(ref OpenSet s0, OpenSet s1)
{
    int n;
    for (n = 0; n <= SHORT(s1.length) - 1; ++n)
    {
        s0[n] = -s1[n];
    }
}

void Union(ref OpenSet s0, OpenSet s1, OpenSet s2)
{
    int n;
    uint s;
    for (n = 0; n <= SHORT(s1.length) - 1; ++n)
    {
        s = s1[n] + s2[n];
        s0[n] = s;
    }
}

void Difference(ref OpenSet s0, OpenSet s1, OpenSet s2)
{
    int n;
    uint s;
    for (n = 0; n <= SHORT(s1.length) - 1; ++n)
    {
        s = s1[n] - s2[n];
        s0[n] = s;
    }
}

void Intersection(ref OpenSet s0, OpenSet s1, OpenSet s2)
{
    int n;
    uint s;
    for (n = 0; n <= SHORT(s1.length) - 1; ++n)
    {
        s = s1[n] * s2[n];
        s0[n] = s;
    }
}

void SymmetricDifference(ref OpenSet s0, OpenSet s1, OpenSet s2)
{
    int n;
    uint s;
    for (n = 0; n <= SHORT(s1.length) - 1; ++n)
    {
        s = s1[n] / s2[n];
        s0[n] = s;
    }
}

bool In(OpenSet s1, int n)
{
    return MOD(n, M) in s1[DIV(n, M)];
}

bool Included(OpenSet s1, OpenSet s2)
{
    int n;
    for (n = 0; n <= SHORT(s2.length) - 1; ++n)
    {
        if (s1[n] + s2[n] != s1[n])
        {
            return false;
        }
    }
    return true;
}

bool IsEmpty(OpenSet s1)
{
    int n;
    for (n = 0; n <= SHORT(s1.length) - 1; ++n)
    {
        if (s1[n] != Set)
        {
            return false;
        }
    }
    return true;
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

bool Disjoint(OpenSet s1, OpenSet s2)
{
    int n;
    for (n = 0; n <= SHORT(s1.length) - 1; ++n)
    {
        if (s1[n] * s2[n] != Set)
        {
            return false;
        }
    }
    return true;
}

int nSetsUsed(OpenSet s1)
{
    return SHORT(s1.length);
}

uint ConvertToSET(OpenSet s1, int Index)
{
    return s1[Index];
}

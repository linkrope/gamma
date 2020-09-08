module runtime;

import std.math;

alias ABS = abs;

char CHR(int x)
{
    import std.conv : to;
    return x.to!char;
}

int ORD(char c)
{
    return c;
}

void INC(T)(ref T v, T x = 1)
{
    v += x;
}

void DEC(T)(ref T v, T x = 1)
{
    v -= x;
}

void COPY(T)(string x, ref T v)
{
    import std.algorithm : copy, fill;

    fill(v[], '\0');
    copy(x[], v[]);
}

void NEW(T)(ref T v)
{
    v = new T;
}

void NEW(T)(ref T[] v, size_t length)
{
    v = new T[length];
}

void NEW(T)(ref T[][] v, size_t x, size_t y)
{
    v = new T[][x];
    foreach (ref w; v)
        w = new T[y];
}

uint SET(size_t[] elements...)
{
    import std.algorithm : map, reduce;

    return reduce!"a | b"(0, elements.map!(element => 1 << element));
}

bool IN(uint set, size_t x)
{
    return (set & SET(x)) != 0;
}

void INCL(ref uint set, size_t x)
{
    set |= SET(x);
}

void EXCL(ref uint set, size_t x)
{
    set &= ~SET(x);
}

uint SHORT(ulong x)
{
    import std.conv : to;

    return x.to!uint;
}

/**
 * Returns the quotient for a floored division.
 */
long DIV(long D, long d)
{
    long q = D / d;
    const r = D % d;

    if ((r > 0 && d < 0) || (r < 0 && d > 0))
        --q;
    return q;
}

@("compute DIV for floored division")
unittest
{
    assert(DIV(8, 3) == 2);
    assert(DIV(8, -3) == -3);
    assert(DIV(-8, 3) == -3);
    assert(DIV(-8, -3) == 2);
}

/**
 * Returns the remainder for a floored division.
 */
long MOD(long D, long d)
{
    long r = D % d;

    if ((r > 0 && d < 0) || (r < 0 && d > 0))
        r += d;
    return r;
}

@("compute MOD for floored division")
unittest
{
    assert(MOD(8, 3) == 2);
    assert(MOD(8, -3) == -1);
    assert(MOD(-8, 3) == 1);
    assert(MOD(-8, -3) == -2);
}

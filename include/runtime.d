module runtime;

import std.math;

alias ABS = abs;

void ASSERT(bool condition, int code = 0)
{
    import std.exception : enforce;
    import  std.format : format;

    enforce(condition, format!"code: %s"(code));
}

char CHR(int x)
{
    import std.conv : to;
    return x.to!char;
}

int ORD(char c)
{
    return c;
}

void INC(T)(ref T v, T x)
{
    v += x;
}

void DEC(T)(ref T v, T x)
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

uint SET(uint x)
{
    return x;
}

bool IN(uint set, size_t x)
{
    return (set & 1 << x) != 0;
}

void INCL(ref uint set, size_t x)
{
    set |= 1 << x;
}

void EXCL(ref uint set, size_t x)
{
    set &= ~(1 << x);
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

///
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

///
unittest
{
    assert(MOD(8, 3) == 2);
    assert(MOD(8, -3) == -1);
    assert(MOD(-8, 3) == 1);
    assert(MOD(-8, -3) == -2);
}

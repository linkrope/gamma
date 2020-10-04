module set;

import std.bitmanip;

version (unittest) import std.format;

alias OpenSet = BitArray;

void New(ref OpenSet s0, int MaxElem)
{
    s0 = BitArray(null);
    s0.length = MaxElem + 1;
}

@("create new empty set")
unittest
{
    BitArray set;

    New(set, 32);

    assert(format!"%b"(set) == "0_00000000_00000000_00000000_00000000");
}

void Empty(ref OpenSet s0)
{
    s0[] = false;
}

@("reset set")
unittest
{
    auto set = BitArray([0, 1, 0, 0, 1, 1, 0, 1]);

    Empty(set);

    assert(format!"%b"(set) == "00000000");
}

void Incl(ref OpenSet s0, int n)
{
    s0[n] = true;
}

@("include element in set")
unittest
{
    auto set = BitArray([0, 1, 0, 0, 1, 1, 0, 1]);

    Incl(set, 3);

    assert(format!"%b"(set) == "01011101");
}

void Excl(ref OpenSet s0, int n)
{
    s0[n] = false;
}

@("exclude element from set")
unittest
{
    auto set = BitArray([0, 1, 0, 0, 1, 1, 0, 1]);

    Excl(set, 5);

    assert(format!"%b"(set) == "01001001");
}

void Assign(ref OpenSet s0, OpenSet s1)
{
    s0 = s1.dup;
}

@("copy set")
unittest
{
    auto set = BitArray([0, 1, 0, 0, 1, 1, 0, 1]);

    Assign(set, BitArray([1, 0, 1, 1, 0, 0, 1, 0]));

    assert(format!"%b"(set) == "10110010");
}

void Complement(ref OpenSet s0, OpenSet s1)
{
    s0 = ~s1;
}

@("compute complement of set")
unittest
{
    auto set = BitArray([0, 1, 0, 0, 1, 1, 0, 1]);

    Complement(set, BitArray([0, 0, 0, 0, 0, 0, 0, 0]));

    assert(format!"%b"(set) == "11111111");
}

void Union(ref OpenSet s0, OpenSet s1, OpenSet s2)
{
    s0 = s1 | s2;
}

@("compute set union")
unittest
{
    auto set = BitArray([0, 1, 0, 0, 1, 1, 0, 1]);

    Union(set, BitArray([1, 0, 1, 0, 0, 1, 0, 1]), BitArray([0, 0, 1, 1, 1, 1, 0, 0]));

    assert(format!"%b"(set) == "10111101");
}

void Difference(ref OpenSet s0, OpenSet s1, OpenSet s2)
{
    s0 = s1 & ~s2;
}

@("compute set difference")
unittest
{
    auto set = BitArray([0, 1, 0, 0, 1, 1, 0, 1]);

    Difference(set, BitArray([1, 0, 1, 0, 0, 1, 0, 1]), BitArray([0, 0, 1, 1, 1, 1, 0, 0]));

    assert(format!"%b"(set) == "10000001");
}

void Intersection(ref OpenSet s0, OpenSet s1, OpenSet s2)
{
    s0 = s1 & s2;
}

@("compute set intersection")
unittest
{
    auto set = BitArray([0, 1, 0, 0, 1, 1, 0, 1]);

    Intersection(set, BitArray([1, 0, 1, 0, 0, 1, 0, 1]), BitArray([0, 0, 1, 1, 1, 1, 0, 0]));

    assert(format!"%b"(set) == "00100100");
}

void SymmetricDifference(ref OpenSet s0, OpenSet s1, OpenSet s2)
{
    s0 = s1 ^ s2;
}

@("compute symmetric difference")
unittest
{
    auto set = BitArray([0, 1, 0, 0, 1, 1, 0, 1]);

    SymmetricDifference(set, BitArray([1, 0, 1, 0, 0, 1, 0, 1]), BitArray([0, 0, 1, 1, 1, 1, 0, 0]));

    assert(format!"%b"(set) == "10011001");
}

bool In(OpenSet s1, int n)
{
    return s1[n];
}

@("check if element is included in set")
unittest
{
    auto set = BitArray([0, 1, 0, 0, 1, 1, 0, 1]);

    assert(In(set, 7));
    assert(!In(set, 0));
}

bool Included(OpenSet s1, OpenSet s2)
{
    return s1 >= s2;
}

@("check if one set is included in another set")
unittest
{
    assert(Included(BitArray([1, 0, 1, 0, 0, 1, 0, 1]), BitArray([1, 0, 0, 0, 0, 0, 0, 1])));
    assert(!Included(BitArray([1, 0, 0, 0, 0, 0, 0, 1]), BitArray([1, 0, 1, 0, 0, 1, 0, 1])));
}

bool IsEmpty(OpenSet s1)
{
    return s1.count == 0;
}

@("check if set is empty")
unittest
{
    assert(IsEmpty(BitArray([0, 0, 0, 0, 0, 0, 0, 0])));
    assert(!IsEmpty(BitArray([0, 1, 0, 0, 1, 1, 0, 1])));
}

bool Equal(OpenSet s1, OpenSet s2)
{
    return s1 == s2;
}

@("check if sets are equal")
unittest
{
    assert(Equal(BitArray([0, 1, 0, 0, 1, 1, 0, 1]), BitArray([0, 1, 0, 0, 1, 1, 0, 1])));
    assert(!Equal(BitArray([0, 1, 0, 0, 1, 1, 0, 1]), BitArray([1, 0, 1, 1, 0, 0, 1, 0])));
}

bool Disjoint(OpenSet s1, OpenSet s2)
{
    return (s1 & s2).count == 0;
}

@("check if sets are disjoint")
unittest
{
    assert(Disjoint(BitArray([1, 0, 1, 0, 0, 1, 0, 1]), BitArray([0, 0, 0, 1, 1, 0, 0, 0])));
    assert(!Disjoint(BitArray([1, 0, 1, 0, 0, 1, 0, 1]), BitArray([0, 0, 0, 1, 0, 1, 0, 0])));
}

size_t nSetsUsed(OpenSet s1)
{
    return s1.dim;
}

@("get number of 64-bit sets used to store set")
unittest
{
    BitArray s;

    New(s, 64);

    assert(nSetsUsed(s) == 2);
}

size_t ConvertToSET(OpenSet s1, int Index)
{
    const sets = cast(size_t[]) s1;

    return sets[Index];
}

@("get 64-bit set at given index")
unittest
{
    BitArray s;

    New(s, 127);
    s[64] = true;

    assert(ConvertToSET(s, 1) == 1);
}

size_t SET(size_t[] elements...)
{
    import std.algorithm : map, reduce;

    return reduce!"a | b"(0uL, elements.map!(element => 1uL << element));
}

bool IN(size_t set, size_t x)
{
    return (set & SET(x)) != 0;
}

void INCL(ref size_t set, size_t x)
{
    set |= SET(x);
}

void EXCL(ref size_t set, size_t x)
{
    set &= ~SET(x);
}

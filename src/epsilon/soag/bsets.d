module epsilon.soag.bsets;

import runtime;
import ALists = epsilon.soag.alists;
import std.bitmanip : BitArray;

const firstIndex = ALists.firstIndex;

struct BSetDesc
{
    int Max;
    BitArray BitVektor;
    ALists.AList List;
}

alias BSet = BSetDesc;

/**
 * IN:  Referenzvariabel der Liste, anfängliche Länge der Liste
 * OUT: Referenzvariabel der Liste
 * SEM: Anlegen einer neuen Liste (Speicherplatzreservierung)
 * SEF: -
 */
void New(ref BSet S, int MaxElem) nothrow pure
{
    S = BSet();
    ALists.New(S.List, 16);
    S.BitVektor = BitArray();
    S.BitVektor.length = MaxElem + 1;
    S.Max = MaxElem;
}

/**
 * IN:  Referenzvariabel der Liste
 * OUT: Referenzvariabel der Liste
 * SEM: Löschen des Listeninhalts
 * SEF: -
 */
void Reset(ref BSet S)
{
    ALists.Reset(S.List);
    S.BitVektor[] = false;
}

/**
 * IN:  Referenzvariable der Menge, einzufügendes Element
 * OUT: Referenzvariable der Menge
 * SEM: fügt Element in die Menge ein
 * SEF: -
 */
void Insert(ref BSet S, int Elem) pure
{
    if (Elem <= S.Max)
    {
        if (!S.BitVektor[Elem])
        {
            S.BitVektor[Elem] = true;
            ALists.Append(S.List, Elem);
        }
    }
    else
    {
        throw new Exception("ERROR in eBSet.Insert: element is greater than max element");
    }
}

/**
 * IN:  Referenzvariable der Menge, zu löschendes Element
 * OUT: Referenzvariable der Menge
 * SEM: löscht Element aus der Menge
 * SEF: -
 */
void Delete(ref BSet S, int Elem) pure
{
    if (Elem <= S.Max)
    {
        if (S.BitVektor[Elem])
        {
            S.BitVektor[Elem] = false;

            const i = ALists.IndexOf(S.List, Elem);

            ALists.Delete(S.List, i);
        }
    }
    else
    {
        throw new Exception("ERROR in eBSet.Delete: element is greater than max element");
    }
}

/**
 * IN:  Refrenzvariable der Menge, Element
 * OUT: Referenzvariable der Menge
 * SEM: Testet, ob Element in der Menge ist
 * SEF: -
 */
bool In(BSet S, int Elem) @nogc nothrow pure
{
    return S.BitVektor[Elem];
}

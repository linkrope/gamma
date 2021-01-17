module soag.eALists;

import runtime;

const firstIndex = 0;

struct AListDesc
{
    int Last;
    int[] Elem;
}

alias AList = AListDesc;

void Expand(ref AList List) nothrow pure @safe
{
    assert(List.Elem.length < DIV(int.max, 2));

    auto List1 = new int[2 * List.Elem.length + 1];

    for (int i = firstIndex; i <= List.Last; ++i)
        List1[i] = List.Elem[i];
    List.Elem = List1;
}

/**
 * IN:  Referenzvariabel der Liste, anfängliche Länge der Liste
 * OUT: Referenzvariabel der Liste
 * SEM: Anlegen einer neune Liste (Speicherplatzreservierung)
 * SEF: -
 */
void New(ref AList List, int Len) nothrow pure @safe
{
    List = AList();
    List.Last = -1;
    List.Elem = new int[Len];
}

/**
 * IN:  Referenzvariabel der Liste
 * OUT: Referenzvariabel der Liste
 * SEM: Löschen des Listeninhalts
 * SEF: -
 */
void Reset(ref AList List) @nogc nothrow pure @safe
{
    List.Last = -1;
}

/**
 * IN:  Referenzvariabel der Liste, Index des zu löschenden Elements
 * OUT: Referenzvariabel der Liste
 * SEM: Löschen eines Elements
 * SEF: Auf die Reihenfolge innerhalb der Liste
 */
void Delete(ref AList List, int Index) @nogc nothrow pure @safe
{
    if (Index >= firstIndex)
    {
        List.Elem[Index] = List.Elem[List.Last];
        --List.Last;
    }
}

/**
 * IN:  Referenzvariabel der Liste, Wert des Elements
 * OUT: Referenzvariabel der Liste
 * SEM: Anhängen des Elements am Ende der Liste
 * SEF: -
 */
void Append(ref AList List, int Value) nothrow pure @safe
{
    if (List.Last + 1 >= List.Elem.length)
        Expand(List);
    ++List.Last;
    List.Elem[List.Last] = Value;
}

/**
 * IN:  Referenzvariabel der Liste, gesuchter Wert
 * OUT: Referenzvariabel der Liste, Index des ges. Wertes
 * SEM: Liefert den Index des gesuchten Wertes;
 *      Nach einer Delete-Aktion ist dieser Wert inkonsistent!
 * SEF: -
*/
int IndexOf(ref AList List, int Value) @nogc nothrow pure @safe
{
    int i = firstIndex;

    while (List.Elem[i] != Value && i <= List.Last)
        ++i;
    return (i <= List.Last) ? i : -1;
}

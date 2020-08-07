module soag.eALists;

import runtime;

const firstIndex = 0;
alias OpenList = int[];

struct AListDesc
{
    int Last;
    OpenList Elem;
}

alias AList = AListDesc;

void Expand(ref AList List)
{
    OpenList List1;
    int i;
    if (List.Elem.length < DIV(int.max, 2))
    {
        NEW(List1, 2 * List.Elem.length + 1);
    }
    else
    {
        assert(0);
    }
    for (i = firstIndex; i <= List.Last; ++i)
    {
        List1[i] = List.Elem[i];
    }
    List.Elem = List1;
}

/**
 * IN:  Referenzvariabel der Liste, anfängliche Länge der Liste
 * OUT: Referenzvariabel der Liste
 * SEM: Anlegen einer neune Liste (Speicherplatzreservierung)
 * SEF: -
 */
void New(ref AList List, int Len)
{
    List = AList();
    List.Last = -1;
    NEW(List.Elem, Len);
}

/**
 * IN:  Referenzvariabel der Liste
 * OUT: Referenzvariabel der Liste
 * SEM: Löschen des Listeninhalts
 * SEF: -
 */
void Reset(ref AList List)
{
    List.Last = -1;
}

/**
 * IN:  Referenzvariabel der Liste, Index des zu löschenden Elements
 * OUT: Referenzvariabel der Liste
 * SEM: Löschen eines Elements
 * SEF: Auf die Reihenfolge innerhalb der Liste
 */
void Delete(ref AList List, int Index)
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
void Append(ref AList List, int Value)
{
    if (List.Last + 1 >= List.Elem.length)
    {
        Expand(List);
    }
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
int IndexOf(ref AList List, int Value)
{
    int i;
    i = firstIndex;
    while (List.Elem[i] != Value && i <= List.Last)
    {
        ++i;
    }
    if (i <= List.Last)
    {
        return i;
    }
    else
    {
        return -1;
    }
}

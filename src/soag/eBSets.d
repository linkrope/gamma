module soag.eBSets;

import runtime;
import IO = eIO;
import Sets = eSets;
import ALists = soag.eALists;

const firstIndex = ALists.firstIndex;

struct BSetDesc
{
    int Max;
    Sets.OpenSet BitVektor;
    ALists.AList List;
}

alias BSet = BSetDesc;

/**
 * IN:  Referenzvariabel der Liste, anfängliche Länge der Liste
 * OUT: Referenzvariabel der Liste
 * SEM: Anlegen einer neuen Liste (Speicherplatzreservierung)
 * SEF: -
 */
void New(ref BSet S, int MaxElem)
{
    S = BSet();
    ALists.New(S.List, 16);
    Sets.New(S.BitVektor, MaxElem);
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
    int i;
    ALists.Reset(S.List);
    Sets.Empty(S.BitVektor);
}

/**
 * IN:  Referenzvariable der Menge, einzufügendes Element
 * OUT: Referenzvariable der Menge
 * SEM: fügt Element in die Menge ein
 * SEF: -
 */
void Insert(ref BSet S, int Elem)
{
    if (Elem <= S.Max)
    {
        if (!Sets.In(S.BitVektor, Elem))
        {
            Sets.Incl(S.BitVektor, Elem);
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
void Delete(ref BSet S, int Elem)
{
    int i;
    if (Elem <= S.Max)
    {
        if (Sets.In(S.BitVektor, Elem))
        {
            Sets.Excl(S.BitVektor, Elem);
            i = ALists.IndexOf(S.List, Elem);
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
bool In(BSet S, int Elem)
{
    return Sets.In(S.BitVektor, Elem);
}

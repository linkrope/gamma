module soag.eASets;

import runtime;
import IO = eIO;
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
int i;

/**
 * IN:  Referenzvariabel der Liste, anfängliche Laenge der Liste
 * OUT: Referenzvariabel der Liste
 * SEM: Anlegen einer neuen Liste (Speicherplatzreservierung)
 * SEF: -
 */
void New(ref ASet S, int MaxElem)
{
    S = ASet();
    ALists.New(S.List, MaxElem + 1);
    S.Max = MaxElem;
    for (i = firstIndex; i <= MaxElem; ++i)
    {
        S.List.Elem[i] = noelem;
    }
}

/**
 * IN:  Referenzvariabel der Liste
 * OUT: Referenzvariabel der Liste
 * SEM: Löschen des Listeninhalts
 * SEF: -
*/
void Reset(ref ASet S)
{
    int i;
    ALists.Reset(S.List);
    for (i = firstIndex; i <= S.Max; ++i)
    {
        S.List.Elem[i] = noelem;
    }
}

/**
 * IN:  Referenzvariabel der Menge
 * OUT: Referenzvariabel derMenge
 * SEM: Test, ob die Menge leer ist
 * SEF: -
 */
bool IsEmpty(ref ASet S)
{
    return S.List.Last < firstIndex;
}

/**
 * IN:  Referenzvariable der Menge, einzufügendes Element
 * OUT: Referenzvariable der Menge
 * SEM: fügt Element in die Menge ein
 * SEF: -
 */
void Insert(ref ASet S, int Elem)
{
    if (Elem <= S.Max)
    {
        if (Elem <= S.List.Last)
        {
            if (S.List.Elem[Elem] != Elem)
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
            if (S.List.Elem[Elem] <= noelem)
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
    else
    {
        throw new Exception("ERROR in eASet.Insert: element is greater than max element");
    }
}

/**
 * IN:  Referenzvariable der Menge, zu löschendes Element
 * OUT: Referenzvariable der Menge
 * SEM: löscht Element aus der Menge
 * SEF: -
 */
void Delete(ref ASet S, int Elem)
{
    int Last;
    if (Elem <= S.Max)
    {
        if (Elem <= S.List.Last)
        {
            if (S.List.Elem[Elem] == Elem)
            {
                if (Elem == S.List.Last)
                {
                    S.List.Elem[S.List.Last] = noelem;
                }
                else
                {
                    S.List.Elem[Elem] = S.List.Elem[S.List.Last];
                    S.List.Elem[S.List.Last] = Elem;
                }
                --S.List.Last;
            }
        }
        else
        {
            if (S.List.Elem[Elem] > noelem)
            {
                if (S.List.Elem[Elem] == S.List.Last)
                {
                    S.List.Elem[S.List.Last] = noelem;
                }
                else
                {
                    S.List.Elem[S.List.Elem[Elem]] = S.List.Last;
                    S.List.Elem[S.List.Last] = S.List.Elem[Elem];
                }
                S.List.Elem[Elem] = noelem;
                --S.List.Last;
            }
        }
    }
    else
    {
        throw new Exception("ERROR in eASet.Delete: element is greater than max element");
    }
}

/**
 * IN:  Referenzvariable der Menge, Element
 * OUT: Referenzvariable der Menge
 * SEM: Testet, ob Element in der Menge ist
 * SEF: -
 */
bool In(ASet S, int Elem)
{
    if (Elem > S.List.Last)
    {
        return S.List.Elem[Elem] > noelem;
    }
    else
    {
        return S.List.Elem[Elem] == Elem;
    }
}

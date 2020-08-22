module soag.eSOAGHash;

import runtime;
import SOAG = soag.eSOAG;
import IO = eIO;

const empty = 0;

class HashEntry
{
    SOAG.Instruction Instr;
}

alias OpenHashTab = HashEntry[];
OpenHashTab HashTab;

int MaxHashTabIndex;
int MaxTry;
int V4711;
int V711;

void Wr(char[] S, int I)
{
    IO.WriteString(IO.Msg, S);
    IO.WriteInt(IO.Msg, I);
    IO.WriteLn(IO.Msg);
    IO.Update(IO.Msg);
}

/**
 * SEM: leert die Hash-Tabelle
 */
void Reset()
{
    int i;
    MaxTry = 0;
    for (i = 0; i <= MaxHashTabIndex - 1; ++i)
    {
        HashTab[i] = null;
    }
}

/**
 * IN:  maximale Anzahl an Affixparametern in einer Regel
 * OUT: -
 * SEM: reserviert Speicher für die Hash-Tabelle und setzt die max. Hash-Adresse
 */
void Init(int MaxAffInRule)
{
    import std.conv : to;
    import std.math : log2;

    int Exp;
    int i;
    // Exp = SHORT(ENTIER(Math.ln(MaxAffInRule) / Math.ln(2)) + 1);
    Exp = log2(MaxAffInRule).to!int + 1;
    MaxHashTabIndex = 2;
    for (i = 2; i <= Exp; ++i)
    {
        MaxHashTabIndex = MaxHashTabIndex * 2;
    }
    NEW(HashTab, MaxHashTabIndex);
    Reset;
}

/**
 * IN:  Instruktion aus der Visit-Sequenz, kein NIL !
 * OUT: Index in der Hash-Tabelle
 * SEM: Ermittlung Indexes in der Hash-Tabelle
 */
int HashIndex(ref SOAG.Instruction I)
{
    import std.conv : to;

    int Index;
    int Index0;
    int Try;
    bool notfound;

    /**
     * Fehler im Compiler: kann keine Integerkonstanten > 128 in Multiplikationen verarbeiten
     * IN:  Instruktion
     * OUT: -
     * SEM: Realisierung der Hash-Funktion
     */
    int HashFun(ref SOAG.Instruction I)
    {
        import std.conv : to;

        int Index;

        if (cast(SOAG.Visit) I !is null)
            Index = 100 + V4711 * (cast(SOAG.Visit) I).SymOcc + V711 * (cast(SOAG.Visit) I).VisitNo;
        else if (cast(SOAG.Leave) I)
            Index = 200 + V4711 * (cast(SOAG.Leave) I).VisitNo;
        else if (cast(SOAG.Call) I !is null)
            Index = 300 + V4711 * (cast(SOAG.Call)I).SymOcc;
        else
            Index = 0;
        return MOD(Index, MaxHashTabIndex).to!int;
    }

    Try = 0;
    Index0 = HashFun(I);
    Index = Index0;
    if (HashTab[Index] is null)
    {
        notfound = false;
    }
    else
    {
        notfound = !SOAG.isEqual(I, HashTab[Index].Instr);
    }
    while (notfound)
    {
        ++Try;
        Index = MOD(Index0 - Try * (DIV(Index0, 2) * 2 + 1), MaxHashTabIndex).to!int;
        if (HashTab[Index] is null)
        {
            notfound = false;
        }
        else
        {
            notfound = !SOAG.isEqual(I, HashTab[Index].Instr);
        }
    }
    if (MaxTry < Try)
    {
        MaxTry = Try;
    }
    return Index;
}

/**
 * IN:  Instruktion aus der Visit-Sequenz
 * OUT: boolscher Wert
 * SEM: Test, ob die Instruktion schon in der Hash-Tabelle enthalten ist
 */
bool IsIn(SOAG.Instruction I)
{
    int Index;
    if (I is null)
    {
        return true;
    }
    else
    {
        Index = HashIndex(I);
        return HashTab[Index] !is null;
    }
}

/**
 * IN:  Instruktion der Visit-Sequenz
 * OUT: -
 * SEM: fügt die Instruktion in die Hash-Tabelle ein
 */
void Enter(SOAG.Instruction I)
{
    int Index;
    HashEntry Entry;
    if (I !is null)
    {
        Index = HashIndex(I);
        NEW(Entry);
        Entry.Instr = I;
        HashTab[Index] = Entry;
    }
}

static this()
{
    V4711 = 4711;
    V711 = 711;
}

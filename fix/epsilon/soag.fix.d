module $;

import io : Position;
import log;
import runtime;
import Stacks = epsilon.soag.listacks;
import std.stdio;

const nil = -1;
const initialStorageSize = 128;
const syntacticPart = 0;
const hyperArityConst = $;
$
alias TreeType = long;
// alias HeapType = long;
alias IndexType = long;

TreeType[] Tree;
Position[] PosTree;
long ErrorCounter;
int AffixVarCount;
Position Pos;
File Out;
HeapType RefIncVar;

class SemTreeEntry
{
    long Rule;
    Position Pos;
    IndexType Adr;
    IndexType VarInd;
}

SemTreeEntry[] SemTree;
HeapType[] Var;
HeapType[] AffPos;
IndexType NextSemTree;
IndexType NextVar;

// insert evaluator global things
$
void ExpandSemTree()
{
    auto SemTree1 = new SemTreeEntry[2 * SemTree.length];

    for (IndexType i = 0; i < SemTree.length; ++i)
        SemTree1[i] = SemTree[i];
    SemTree = SemTree1;
}

void ExpandVar()
{
    auto Var1 = new HeapType[2 * Var.length];

    for (IndexType i = 0; i < Var.length; ++i)
        Var1[i] = Var[i];
    Var = Var1;
}

// Predicates

$

void Init()
{
    SemTree = new SemTreeEntry[initialStorageSize];
    AffPos = new HeapType[$];
    Var = new HeapType[8 * initialStorageSize];
    NextSemTree = 0;
    NextVar = 0;
    AffixVarCount = 0;
    $
}

void TraverseSyntaxTree(TreeType[] Tree1, Position[] PosTree1, long ErrCounter, TreeType Adr, int HyperArity,
        bool info_, bool write)
{
    IndexType StartSymbol;
    HeapType V1;

    if (HyperArity != hyperArityConst)
        throw new Exception("internal error: 'arityConst' is wrong");
    Tree = Tree1;
    PosTree = PosTree1;
    ErrorCounter = ErrCounter;
    Init;
    StartSymbol = NextSemTree;
    SemTree[StartSymbol] = new SemTreeEntry;
    SemTree[StartSymbol].Adr = Adr;
    SemTree[StartSymbol].Rule = MOD($Tree[Adr], hyperArityConst);
    ++NextSemTree;
    Visit(StartSymbol, syntacticPart);
    Visit(StartSymbol, 1);
    V1 = AffPos[$];
    if (ErrorCounter > 0)
    {
        info!"errors detected: %s"(ErrorCounter);
    }
    else
    {
        $
    }
    $
    if (info_)
    {
        info!"semantic tree of %s affixes uses %s affix variables, with:"(AffixVarCount, NextVar);
        info!"%s stacks"($);
        info!"%s global variables"($);
    }
    Tree = null;
    PosTree = null;
    SemTree = null;
    Var = null;
    AffPos = null;
}

// END $.
$

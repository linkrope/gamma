module $;

import runtime;
import IO = eIO;
import Stacks = soag.eLIStacks;

const nil = -1;
const initialStorageSize = 128;
const syntacticPart = 0;
const hyperArityConst = $;
$
alias TreeType = long;
alias OpenTree = TreeType[];
alias OpenPos = IO.Position[];
// alias HeapType = long;
alias IndexType = long;

OpenTree Tree;
OpenPos PosTree;
long ErrorCounter;
int AffixVarCount;
IO.Position Pos;
IO.TextOut Out;
HeapType RefIncVar;

class SemTreeEntry
{
    long Rule;
    IO.Position Pos;
    IndexType Adr;
    IndexType VarInd;
}

alias OpenSemTree = SemTreeEntry[];
alias OpenVar = HeapType[];
alias OpenAffPos = HeapType[];

OpenSemTree SemTree;
OpenVar Var;
OpenAffPos AffPos;
IndexType NextSemTree;
IndexType NextVar;

// insert evaluator global things
$
void ExpandSemTree()
{
    OpenSemTree SemTree1;
    IndexType i;
    NEW(SemTree1, 2 * SemTree.length);
    for (i = 0; i <= SemTree.length - 1; ++i)
    {
        SemTree1[i] = SemTree[i];
    }
    SemTree = SemTree1;
}

void ExpandVar()
{
    OpenVar Var1;
    IndexType i;
    NEW(Var1, 2 * Var.length);
    for (i = 0; i <= Var.length - 1; ++i)
    {
        Var1[i] = Var[i];
    }
    Var = Var1;
}

// Predicates

$

void Init()
{
    NEW(SemTree, initialStorageSize);
    NEW(AffPos, $);
    NEW(Var, 8 * initialStorageSize);
    NextSemTree = 0;
    NextVar = 0;
    AffixVarCount = 0;
    $
}

void TraverseSyntaxTree(OpenTree Tree1, OpenPos PosTree1, long ErrCounter, TreeType Adr, int HyperArity)
{
    IndexType StartSymbol;
    HeapType V1;
    if (HyperArity != hyperArityConst)
    {
        throw new Exception("internal error: 'arityConst' is wrong");
    }
    Tree = Tree1;
    PosTree = PosTree1;
    ErrorCounter = ErrCounter;
    Init;
    StartSymbol = NextSemTree;
    NEW(SemTree[StartSymbol]);
    SemTree[StartSymbol].Adr = Adr;
    SemTree[StartSymbol].Rule = MOD($Tree[Adr], hyperArityConst);
    ++NextSemTree;
    Visit(StartSymbol, syntacticPart);
    Visit(StartSymbol, 1);
    V1 = AffPos[$];
    if (ErrorCounter > 0)
    {
        IO.WriteText(IO.Msg, "  ");
        IO.WriteInt(IO.Msg, ErrorCounter);
        IO.WriteText(IO.Msg, " errors detected\n");
        IO.Update(IO.Msg);
    }
    else
    {
        $
    }
    $
    if (IO.IsOption('i'))
    {
        IO.WriteText(IO.Msg, "\tsemantic tree of ");
        IO.WriteInt(IO.Msg, AffixVarCount);
        IO.WriteText(IO.Msg, " affixes uses ");
        IO.WriteInt(IO.Msg, NextVar);
        IO.WriteText(IO.Msg, " affix variables, with\n\t\t");
        IO.WriteInt(IO.Msg, $);
        IO.WriteText(IO.Msg, " stacks and\n\t\t");
        IO.WriteInt(IO.Msg, $);
        IO.WriteText(IO.Msg, " global variables\n");
    }
    Tree = null;
    PosTree = null;
    SemTree = null;
    Var = null;
    AffPos = null;
}

// END $.
$

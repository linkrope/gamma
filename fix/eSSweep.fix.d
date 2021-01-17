module $;

import IO = eIO;
import io : Position;
import runtime;
import std.stdio;

const hyperArityConst = $;
alias TreeType = long;
// alias HeapType = long;

TreeType[] Tree;
Position[] PosTree;
long ErrorCounter;
Position Pos;
IO.TextOut Out;

$

void TraverseSyntaxTree(TreeType[] Tree1, Position[] PosTree1, long ErrCounter, TreeType Adr, int HyperArity,
        bool info, bool write)
{
    HeapType V1;

    if (HyperArity != hyperArityConst)
    {
        throw new Exception("internal error: 'arityConst' is wrong");
    }
    Tree = Tree1;
    PosTree = PosTree1;
    ErrorCounter = ErrCounter;
    $(Adr, V1);
    if (ErrorCounter > 0)
    {
        IO.Msg.write("  ");
        IO.Msg.write(ErrorCounter);
        IO.Msg.write(" errors detected\n");
        IO.Msg.flush;
    }
    else
    {
        $
    }
    $
    Tree = null;
    PosTree = null;
}

// END $.
$

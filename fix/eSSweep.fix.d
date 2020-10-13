module $;

import IO = eIO;
import io : Position;
import runtime;
import std.stdio;

const hyperArityConst = $;
alias TreeType = long;
alias OpenTree = TreeType[];
alias OpenPos = Position[];
// alias HeapType = long;

OpenTree Tree;
OpenPos PosTree;
long ErrorCounter;
Position Pos;
IO.TextOut Out;

$

void TraverseSyntaxTree(OpenTree Tree1, OpenPos PosTree1, long ErrCounter, TreeType Adr, int HyperArity,
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

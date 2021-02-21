module $;

import IO = epsilon.io : TextOut;
import io : Position;
import log;
import runtime;

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
        bool info_, bool write)
{
    import std.exception : enforce;
    HeapType V1;

    enforce(HyperArity == hyperArityConst,
        "internal error: wrong arity constant");

    Tree = Tree1;
    PosTree = PosTree1;
    ErrorCounter = ErrCounter;
    $(Adr, V1);
    if (ErrorCounter > 0)
    {
        info!"errors detected: %s"(ErrorCounter);
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

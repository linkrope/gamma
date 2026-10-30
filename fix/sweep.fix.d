module $;

import io : Position;
import log;
import runtime;
import std.stdio;

const hyperArityConst = $;
alias TreeType = long;
// alias HeapType = long;

TreeType[] Tree;
Position[] PosTree;
long ErrorCounter;
Position Pos;
File Out;

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
        import core.stdc.stdlib : exit, EXIT_FAILURE;

        info!"errors detected: %s"(ErrorCounter);
        exit(EXIT_FAILURE);
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

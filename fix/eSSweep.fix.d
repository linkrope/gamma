module $;
import runtime;
import IO = eIO;

const hyperArityConst = $;
alias TreeType = long;
alias OpenTree = TreeType[];
alias OpenPos = IO.Position[];
OpenTree Tree;
OpenPos PosTree;
long ErrorCounter;
IO.Position Pos;
IO.TextOut Out;
$
void TraverseSyntaxTree(OpenTree SyntaxTree, OpenPos PosHeap, long ErrCounter,
        TreeType Adr, int HyperArity)
{
    HeapType V1;
    if (HyperArity != hyperArityConst)
    {
        throw new Exception("internal error: 'arityConst' is wrong");
    }
    Tree = SyntaxTree;
    PosTree = PosHeap;
    ErrorCounter = ErrCounter;
    $(Adr, V1);
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
    Tree = null;
    PosTree = null;
}

$

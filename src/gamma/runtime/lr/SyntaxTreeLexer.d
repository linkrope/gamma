module gamma.runtime.lr.SyntaxTreeLexer;

import gamma.runtime.Lexer;
import gamma.runtime.SyntaxTree : SyntaxTreeNode;

public interface SyntaxTreeLexer : Lexer
{
    /// The syntax-tree occurrence for the most recently returned token.
    SyntaxTreeNode syntaxTreeNode() const;
}

module gamma.runtime.lr.ParseTreeLexer;

import gamma.runtime.Lexer;
import gamma.runtime.ParseTree : ParseNode;

public interface ParseTreeLexer : Lexer
{
    /// The node for the most recently returned terminal or lexical nonterminal.
    const(ParseNode)* parseNode() const;
}

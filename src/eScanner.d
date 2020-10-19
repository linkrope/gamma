module eScanner;

import epsilon.lexer;
import io : Input, Position;
import symbols : SymbolTable;

const eot = Token.end;
const str = Token.string_;
const num = Token.number;
const ide = Token.name;

SymbolTable symbolTable;
Lexer lexer;
int Val;
Position Pos;

void Init(Input input)
{
    symbolTable = new SymbolTable;
    lexer = Lexer(input, symbolTable);
}

public string repr(int Id)
{
    return symbolTable.symbol(Id);
}

void Get(ref char Tok)
{
    import std.conv : to;

    static bool start = true;

    if (start)
        start = false;
    else
        lexer.popFront;
    Tok = lexer.front.to!char;
    Val = lexer.value.to!int;
    Pos = lexer.position;
}

size_t ErrorCounter()
{
    return lexer.ok ? 0 : 1;
}

module epsilon.lexer;

import io : Input, Position;
import std.uni;
import symbols : SymbolTable;

struct Lexer
{
    private Input input;

    private SymbolTable symbolTable;

    invariant (symbolTable !is null);

    private dchar token;

    private size_t value_;

    private Position position_;

    private size_t errorCount = 0;

    this(Input input, SymbolTable symbolTable)
    in (symbolTable !is null)
    {
        this.input = input;
        this.symbolTable = symbolTable;
        readToken;
    }

    bool empty() const @nogc nothrow pure @safe
    {
        return token == Token.end;
    }

    dchar front() const @nogc nothrow pure @safe
    {
        return token;
    }

    void popFront()
    {
        readToken;
    }

    private void readToken()
    {
        scope (exit)
            addTrace;
        while (true)
        {
            while (input.next.isWhite)
                input.popFront;
            position_ = input.position;
            if (input.empty)
            {
                token = Token.end;
                return;
            }
            if (input.front == '/')
            {
                token = input.front;
                input.popFront;
                if (input.next == '/')
                    readLineComment;
                else if (input.next == '*')
                    readBlockComment;
                else
                    return;
            }
            else
            {
                break;
            }

        }
        if (input.front == '"' || input.front == '\'')
        {
            token = Token.string_;
            readString;
        }
        else if (input.front == '`')
        {
            token = Token.string_;
            readRawString;
        }
        else if (input.front.isAlpha || input.front == '_')
        {
            token = Token.name;
            readName;
        }
        else if (input.front.isNumber)
        {
            token = Token.number;
            readNumber;
        }
        else
        {
            token = input.front;
            input.popFront;
        }
    }

    @("read empty input")
    unittest
    {
        with (fixture(null))
        {
            assert(lexer.empty);
            assert(lexer.front == Token.end);
            assert(lexer.ok);
        }
    }

    @("read special character")
    unittest
    {
        with (fixture(":"))
        {
            assert(lexer.front == ':');
            assert(lexer.ok);
        }
    }

    @("read variable")
    unittest
    {
        with (fixture("foo 42"))
        {
            assert(lexer.front == Token.name);
            assert(symbolTable.symbol(lexer.value) == "foo");

            lexer.popFront;

            assert(lexer.front == Token.number);
            assert(symbolTable.symbol(lexer.value) == "42");
            assert(lexer.ok);
        }
    }

    private void readLineComment()
    in (input.next == '/')
    {
        do
            input.popFront;
        while (!input.empty && input.front != '\n');
    }

    @("read line comment")
    unittest
    {
        with (fixture("//\n"))
        {
            assert(lexer.empty);
            assert(lexer.ok);
        }
    }

    private void readBlockComment()
    in (input.next == '*')
    {
        size_t level = 1;
        dchar prev = 0;

        while (true)
        {
            input.popFront;
            if (prev == '/' && input.next == '*')
            {
                input.popFront;
                ++level;
            }
            else if (prev == '*' && input.next == '/')
            {
                input.popFront;
                --level;
                if (level == 0)
                    break;
            }
            if (input.empty)
            {
                addError("comment not closed at end of input");
                break;
            }
            prev = input.front;
        }
    }

    @("read block comment")
    unittest
    {
        with (fixture("/**/"))
        {
            assert(lexer.empty);
            assert(lexer.ok);
        }
    }

    @("read nested block comment")
    unittest
    {
        with (fixture("/*/**/*/"))
        {
            assert(lexer.empty);
            assert(lexer.ok);
        }
    }

    @("read block comment with line comment")
    unittest
    {
        with (fixture("/* // */"))
        {
            assert(lexer.empty);
            assert(lexer.ok);
        }
    }

    @("read invalid block comment")
    unittest
    {
        with (fixture("/*/*/"))
        {
            assert(lexer.empty);
            assert(!lexer.ok);
        }
    }

    /**
     * string:
     *     "'" { character | '\' character } "'"
     *   | '"' { character | '\' character } '"'.
     */
    private void readString()
    in (input.next == '"' || input.next == '\'')
    {
        const quote = input.next;
        const begin = input.index;

        scope (exit)
            value_ = symbolTable.intern(input.sliceFrom(begin));
        do
        {
            input.popFront;
            if (input.next == '\\')
            {
                input.popFront;
                if (!input.empty && input.front != '\n')
                    input.popFront;
            }
            if (input.empty || input.front == '\n')
            {
                addError("string not closed at end of line");
                return;
            }
        }
        while (input.front != quote);
        input.popFront;
    }

    @("read single-quoted string")
    unittest
    {
        with (fixture("'foo'"))
        {
            assert(lexer.front == Token.string_);
            assert(symbolTable.symbol(lexer.value) == "'foo'");
            assert(lexer.ok);
        }
    }

    @("read double-quoted string")
    unittest
    {
        with (fixture(`"foo"`))
        {
            assert(lexer.front == Token.string_);
            assert(symbolTable.symbol(lexer.value) == `"foo"`);
            assert(lexer.ok);
        }
    }

    @("read empty string")
    unittest
    {
        with (fixture(`''`))
        {
            assert(lexer.front == Token.string_);
            assert(symbolTable.symbol(lexer.value) == `''`);
            assert(lexer.ok);
        }
    }

    @("read string with escape sequence")
    unittest
    {
        with (fixture(`'\''`))
        {
            assert(lexer.front == Token.string_);
            assert(symbolTable.symbol(lexer.value) == `'\''`);
            assert(lexer.ok);
        }
    }

    @("read invalid string")
    unittest
    {
        with (fixture(`'foo`))
        {
            assert(lexer.front == Token.string_);
            assert(symbolTable.symbol(lexer.value) == `'foo`);
            assert(!lexer.ok);
        }
    }

    /**
     * string: "`" { character } "`".
     */
    private void readRawString()
    in (input.next == '`')
    {
        const begin = input.index;

        scope (exit)
            value_ = symbolTable.intern(input.sliceFrom(begin));
        do
        {
            input.popFront;
            if (input.empty || input.front == '\n')
            {
                addError("string not closed at end of line");
                return;
            }
        }
        while (input.front != '`');
        input.popFront;
    }

    @("read raw string")
    unittest
    {
        with (fixture("`\\`"))
        {
            assert(lexer.front == Token.string_);
            assert(symbolTable.symbol(lexer.value) == "`\\`");
            assert(lexer.ok);
        }
    }

    /**
     * name: ( letter | "_") { letter | "_" }.
     */
    private void readName()
    in (input.next.isAlpha || input.next == '_')
    {
        const begin = input.index;

        scope (exit)
            value_ = symbolTable.intern(input.sliceFrom(begin));
        do
            input.popFront;
        while (input.next.isAlpha || input.next == '_');
    }

    @("read name")
    unittest
    {
        with (fixture("foo"))
        {
            assert(lexer.front == Token.name);
            assert(symbolTable.symbol(lexer.value) == "foo");
            assert(lexer.ok);
        }
    }

    @("read reserved name")
    unittest
    {
        with (fixture("_foo"))
        {
            assert(lexer.front == Token.name);
            assert(symbolTable.symbol(lexer.value) == "_foo");
            assert(lexer.ok);
        }
    }

    @("read name with umlauts")
    unittest
    {
        with (fixture("äöü"))
        {
            assert(lexer.front == Token.name);
            assert(symbolTable.symbol(lexer.value) == "äöü");
            assert(lexer.ok);
        }
    }

    /**
     * number: digit { digit }.
     */
    private void readNumber()
    in (input.next.isNumber)
    {
        const begin = input.index;

        scope (exit)
            value_ = symbolTable.intern(input.sliceFrom(begin));
        do
            input.popFront;
        while (input.next.isNumber);
    }

    @("read number")
    unittest
    {
        with (fixture("42"))
        {
            assert(lexer.front == Token.number);
            assert(symbolTable.symbol(lexer.value) == "42");
            assert(lexer.ok);
        }
    }

    private void addTrace()
    {
        import log : trace;

        switch (token) with (Token)
        {
            case end:
                trace!"end\n%s"(position_);
                break;
            case string_:
                trace!"string: %s\n%s"(symbolTable.symbol(value_), position_);
                break;
            case name:
                trace!"name: %s\n%s"(symbolTable.symbol(value_), position_);
                break;
            case number:
                trace!"number: %s\n%s"(symbolTable.symbol(value_), position_);
                break;
            default:
                trace!"%s\n%s"(token, position_);
                break;
        }
    }

    private void addError(string message)
    {
        import log : error;

        ++errorCount;
        error!"%s\n%s"(message, position_);
    }

    bool ok() const @nogc nothrow pure @safe
    {
        return errorCount == 0;
    }

    size_t value() const @nogc nothrow pure @safe
    {
        return value_;
    }

    Position position() const @nogc nothrow pure @safe
    {
        return position_;
    }
}

private dchar next(ref Input input)
{
    return input.empty ? 0 : input.front;
}

enum Token : dchar
{
    end = 0,
    string_ = '"',
    name = 'A',
    number = '0',
}

version (unittest)
{
    private auto fixture(string text)
    {
        struct Fixture
        {
            Lexer lexer;

            SymbolTable symbolTable;
        }

        auto symbolTable = new SymbolTable;

        return Fixture(Lexer(Input("name", text), symbolTable), symbolTable);
    }
}

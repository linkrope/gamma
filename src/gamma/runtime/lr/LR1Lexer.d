module gamma.runtime.lr.LR1Lexer;

import io : Input, Position;
import log : error;
import std.uni;

/**
 * Lexer shared by generated parsers.
 *
 * It recognizes source-level tokens by driving generated LR(1) tables.
 * Both generated LALR and ELL parsers can consume its token stream.
 */
public struct LR1Lexer
{
    private Input input;

    private bool ok_ = true;

    public this(Input input)
    {
        this.input = input;
        this.readToken;
    }

    public void popFront()
    in (!this.empty)
    {
        this.input.popFront;
        this.readToken;
    }

    private void readToken()
    {
        while (this.ok_)
        {
            while (!this.input.empty && this.input.front.isWhite)
                this.input.popFront;

            if (this.input.front != '(' || this.input.next != '*')
                break;

            if (!this.skipComment)
                break;
        }
    }

    public bool empty() const
    {
        return this.input.empty;
    }

    public dchar front() const
    in (!this.empty)
    {
        return this.input.front;
    }

    public Position position() const
    {
        return this.input.position;
    }

    public bool ok() const @nogc nothrow pure @safe
    {
        return this.ok_;
    }

    private bool skipComment()
    in (this.input.front == '(' && this.input.next == '*')
    {
        const commentPosition = this.input.position;
        size_t nesting = 0;

        while (!this.input.empty)
        {
            if (this.input.front == '(' && this.input.next == '*')
            {
                this.input.popFront;
                this.input.popFront;
                ++nesting;
            }
            else if (this.input.front == '*' && this.input.next == ')')
            {
                this.input.popFront;
                this.input.popFront;
                --nesting;
                if (nesting == 0)
                    return true;
            }
            else
                this.input.popFront;
        }

        error!"comment not closed at end of input\n%s"(commentPosition);
        this.ok_ = false;
        return false;
    }
}

private dchar next(ref Input input)
{
    Input remaining = input;
    if (!remaining.empty)
        remaining.popFront;
    return remaining.front;
}

@("skip Unicode WhiteSpace before source text")
unittest
{
    import std.string : startsWith;

    LR1Lexer lexer = LR1Lexer(Input("input", "\u2003\t<"));

    assert(lexer.ok);
    assert(!lexer.empty);
    assert(lexer.front == '<');
    assert(lexer.position.toString.startsWith("input:1:3"));
}

@("skip nested comments between source text")
unittest
{
    LR1Lexer lexer = LR1Lexer(Input("input", "(* outer (* inner *) *)  x"));

    assert(lexer.ok);
    assert(lexer.front == 'x');
}

@("reach end of input after trailing WhiteSpace")
unittest
{
    LR1Lexer lexer = LR1Lexer(Input("input", " \n(* *)\t"));

    assert(lexer.ok);
    assert(lexer.empty);
}

@("report an unterminated nested comment")
unittest
{
    import log : Level, levels, logger;
    import std.range : front;
    import std.string : startsWith;

    const previousLevels = levels;
    scope (exit) levels = previousLevels;
    levels = Level.error;
    logger.clear;
    scope (exit) logger.clear;

    LR1Lexer lexer = LR1Lexer(Input("input", "(* outer (* inner *)"));

    assert(!lexer.ok);
    assert(lexer.empty);
    assert(logger.entries.length == 1);
    assert(logger.entries.front.message.startsWith("comment not closed at end of input\n"
        ~ "input:1:1 (* outer (* inner *)"));
}

@("iterate non-WhiteSpace characters")
unittest
{
    LR1Lexer lexer = LR1Lexer(Input("input", "1 2(**)3"));
    dchar[] tokens;

    while (!lexer.empty)
    {
        tokens ~= lexer.front;
        lexer.popFront;
    }

    assert(tokens == "123"d);
}

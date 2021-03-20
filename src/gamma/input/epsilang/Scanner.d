module gamma.input.epsilang.Scanner;

import gamma.util.Position;
import log;
import std.ascii;
import std.conv;
import std.range;
import std.stdio;

class Scanner
{
    private class MarkedLinePrinting : Position
    {
        private size_t pos;

        this(size_t pos)
        {
            this.pos = pos;
        }

        public void markError(string message)
        {
            const lineNumber = this.outer.lineBeginPos.assumeSorted.lowerBound(this.pos + 1).length;
            const beginPos = this.outer.lineBeginPos[lineNumber - 1];
            const endPos = findLineSeparator(this.pos);

            if (beginPos <= this.pos)
            {
                char[] quotation = this.outer.source[beginPos .. endPos];
                char[] mark = new char[this.pos - beginPos + 1];

                foreach (i; 0 .. mark.length - 1)
                    if (this.outer.source[beginPos + i] == '\t')
                        mark[i] = '\t';
                    else
                        mark[i] = ' ';
                mark[mark.length - 1] = '^';
                error!"%s: %s\n%s\n%s"(lineNumber, message, quotation, mark);
            }
            else
                error!"%s: %s"(lineNumber, message);
            ++this.outer.errorCount;
        }

        public override bool opEquals(Object o)
        {
            if (!cast(MarkedLinePrinting) o)
                return false;

            auto that = cast(MarkedLinePrinting) o;

            return this.pos == that.pos && this.scanner == that.scanner;
        }

        public override size_t toHash() nothrow @safe
        {
            return this.pos;
        }

        private Scanner scanner()
        {
            return this.outer;
        }
    }

    static const char END = 0;

    static const char LITERAL = '"';

    static const char NUMBER = '0';

    static const char LEXICAL_VARIABLE = 'a';

    static const char SYNTACTIC_VARIABLE = 'A';

    private char[] source;

    private size_t pos = 0;

    private Position position;

    private string representation;

    private int value;

    private size_t[] lineBeginPos;

    private int errorCount = 0;

    this(File input)
    {
        char[] buffer;

        while (input.readln(buffer))
            this.source ~= buffer;

        this.source ~= END;
        this.lineBeginPos ~= this.pos;
    }

    /**
     * @return the recognized token, coded as a single character
     */
    char read()
    {
        import std.format : format;

        char read()
        {
            char c;

            for (;;)
            {
                c = this.source[this.pos];
                if (c == '\n' || c == '\r')
                    skipLine;
                else if (isWhite(c))
                    ++this.pos;
                else if (c == '/')
                    if (this.source[this.pos + 1] == '/')
                        skipLine;
                    else if (this.source[this.pos + 1] == '*')
                        readComment;
                    else
                        break;
                else if (c == '*')
                    // skip unsupported lexical-variable marker
                    ++this.pos;
                else
                    break;
            }
            this.position = new MarkedLinePrinting(pos);
            this.representation = null;
            if (c == '"')
            {
                this.representation = readLiteral;
                return LITERAL;
            }
            else if (isDigit(c))
            {
                this.value = readNumber;
                return NUMBER;
            }
            else if (isLower(c))
            {
                this.representation = readVariable;
                return LEXICAL_VARIABLE;
            }
            else if (isUpper(c))
            {
                this.representation = readVariable;
                return SYNTACTIC_VARIABLE;
            }
            else if (c != END)
            {
                ++this.pos;
                return c;
            }
            else
                return END;
        }

        const c = read;

        if (levels & Level.trace)
        {
            switch (c)
            {
                case END:
                    getPosition.markError("END");
                    break;
                case LITERAL:
                    getPosition.markError(format!"LITERAL: %s"(getRepresentation));
                    break;
                case NUMBER:
                    getPosition.markError(format!"NUMBER: %s"(getValue));
                    break;
                case LEXICAL_VARIABLE:
                    getPosition.markError(format!"LEXICAL VARIABLE: %s"(getRepresentation));
                    break;
                case SYNTACTIC_VARIABLE:
                    getPosition.markError(format!"SYNTACTIC VARIABLE: %s"(getRepresentation));
                    break;
                default:
                    getPosition.markError(format!"CHAR: %s"(c));
            }
        }
        return c;
    }

    private void readComment()
    in (this.source[this.pos] == '/' && this.source[this.pos + 1] == '*')
    {
        const pos = this.pos;
        int level = 1;
        char c1 = ' ';
        char c2;

        ++this.pos;
        for (;;)
        {
            c2 = this.source[++this.pos];
            if (c1 == '/' && c2 == '*')
            {
                ++this.pos;
                ++level;
                c1 = this.source[this.pos];
            }
            else if (c1 == '*' && c2 == '/')
            {
                ++this.pos;
                if (--level == 0)
                    return;
                c1 = this.source[this.pos];
            }
            else
                c1 = c2;
            while (c1 == '\n' || c1 == '\r')
            {
                skipLine;
                c1 = this.source[this.pos];
            }
            if (c1 == END)
            {
                Position position = new MarkedLinePrinting(pos);

                position.markError("comment not terminated at end of input");
                return;
            }
        }
    }

    private char readEscapeSequence()
    in (this.source[this.pos] == '\\')
    {
        size_t pos = this.pos;
        char c = this.source[++this.pos];
        int value = 0;

        switch (c)
        {
        case 'b':
            c = '\b';
            break;
        case 't':
            c = '\t';
            break;
        case 'n':
            c = '\n';
            break;
        case 'f':
            c = '\f';
            break;
        case 'r':
            c = '\r';
            break;
        case '"':
            c = '"';
            break;
        case '\'':
            c = '\'';
            break;
        case '\\':
            c = '\\';
            break;
        case '0':
        case '1':
        case '2':
        case '3':
        case '4':
        case '5':
        case '6':
        case '7':
            while (isOctalDigit(this.source[this.pos]))
                ++this.pos;
            // TODO: catch ConvException
            value = this.source[pos + 1 .. this.pos].to!int(8);
            if (value > 0xff)
            {
                Position position = new MarkedLinePrinting(pos);

                position.markError("octal character constant out of range");
                return 0;
            }
            return cast(char) value;
        case 'u':
            for (int i = 0; i < 4; ++i)
            {
                if (!isHexDigit(this.source[++this.pos]))
                {
                    Position position = new MarkedLinePrinting(this.pos);

                    position.markError("hexadecimal digit expected");
                    return 0;
                }
            }
            // TODO: catch ConvException
            value = this.source[pos + 2 .. this.pos + 1].to!int(16);
            c = cast(char) value;
            break;
        default:
            if (c != '\n' && c != '\r' && c != END)
            {
                Position position = new MarkedLinePrinting(this.pos);

                position.markError("illegal escape character");
            }
            return 0;
        }
        ++this.pos;
        return c;
    }

    private string readLiteral()
    in (this.source[this.pos] == '"')
    {
        string representation;
        size_t pos = this.pos + 1;
        char c;

        do
        {
            c = this.source[++this.pos];
        }
        while (c != '\\' && c != '"' && c != '\n' && c != '\r' && c != END);
        if (c == '\\')
        {
            char[] buffer;

            buffer ~= this.source[pos .. this.pos];
            do
            {
                if (c == '\\')
                {
                    buffer ~= readEscapeSequence;
                    c = this.source[this.pos];
                }
                else
                {
                    buffer ~= c;
                    c = this.source[++this.pos];
                }
            }
            while (c != '"' && c != '\n' && c != '\r' && c != END);
            representation = buffer.dup;
        }
        else
        {
            if (c == '"' && this.pos == pos)
                this.position.markError("illegal empty string");
            representation = this.source[pos .. this.pos].dup;
        }
        if (c != '"')
        {
            this.position.markError("string not terminated at end of line");
            representation = "";
        }
        else
            ++this.pos;
        return representation;
    }

    private int readNumber()
    in (isDigit(this.source[this.pos]))
    {
        size_t pos = this.pos;
        int value = 0;

        while (isDigit(this.source[this.pos]))
            ++this.pos;
        value = this.source[pos .. this.pos].to!int;
        // TODO: catch ConvException
        if (value > 9999)
        {
            position.markError("number out of range [0, 9999]");
            value = 0;
        }
        return value;
    }

    private string readVariable()
    in (isAlpha(this.source[this.pos]))
    {
        size_t pos = this.pos;

        while (isAlpha(this.source[this.pos]))
            ++this.pos;
        return this.source[pos .. this.pos].dup;
    }

    private void skipLine()
    {
        this.pos = findLineSeparator(this.pos);
        if (this.source[this.pos] != END)
        {
            if (this.source[this.pos] == '\r' && this.source[this.pos + 1] == '\n')
                ++this.pos;
            ++this.pos;
            this.lineBeginPos ~= this.pos;
        }
    }

    private size_t findLineSeparator(size_t pos)
    {
        char c = this.source[pos];

        while (c != '\n' && c != '\r' && c != END)
            c = this.source[++pos];
        return pos;
    }

    Position getPosition()
    {
        return this.position;
    }

    string getRepresentation() const
    {
        return this.representation;
    }

    int getValue() const
    {
        return this.value;
    }

    int getErrorCount() const
    {
        return this.errorCount;
    }
}

module $;

import io : Input, Position;
import log;
import runtime;
import std.uni;

const eot = 0;
const eol = '\n';
const firstChBuf = 0;
const chBufLen = 512;
dchar[chBufLen] ChBuf;
Position[chBufLen] PosBuf;
int CurCh;
int NextCh;
Input In;
const nil = 0;
const firstNode = 1;
const maxTokLen = $;
const maxTok = $;
const undef = 1;
const whitespace = 2;
const comment = int.min;

enum Mode
{
    none,
    ident,
    string_,
}

private Mode mode;

dchar Ch;
dchar StringCh;
Position Pos;
Position PrevPos;

void function(ref int Tok) Get;

void Get2(ref int Tok)
{
    final switch (mode) with (Mode)
    {
        case none:
            while (Ch.isWhite)
                GetCh;
            GetPos;
            if (Ch == eot)
            {
                Tok = eot;
            }
            else if (Ch.isAlphaNum)
            {
                Keyword(Tok);
            }
            else if (Ch == '"' || Ch == '\'')
            {
                StringCh = Ch;
                mode = string_;
                Tok = Node[Ch].Tok;
                GetCh;
            }
            else
            {
                Symbol(Tok);
                if (Tok == comment)
                {
                    Comment;
                    Get(Tok);
                }
            }
            break;
        case ident:
            if (Ch.isAlphaNum)
            {
                GetPos;
                Tok = Node[Ch].Tok;
                GetCh;
            }
            else
            {
                mode = none;
                Get(Tok);
            }
            break;
        case string_:
            if (Ch == eot)
            {
                Tok = eot;
            }
            else
            {
                if (Ch == StringCh || Ch == eol)
                    mode = none;
                GetPos;
                Tok = (Ch in Node) ? Node[Ch].Tok : undef;
                GetCh;
            }
            break;
    }
}

void Get3(ref int Tok)
{
    final switch (mode) with (Mode)
    {
        case none:
            GetPos;
            if (Ch == eot)
            {
                Tok = eot;
            }
            else if (Ch.isWhite)
            {
                do
                    GetCh;
                while (Ch.isWhite);
                Tok = whitespace;
            }
            else if (Ch.isAlphaNum)
            {
                Keyword(Tok);
            }
            else if (Ch == '"' || Ch == '\'')
            {
                StringCh = Ch;
                mode = string_;
                Tok = Node[Ch].Tok;
                GetCh;
            }
            else
            {
                Symbol(Tok);
                if (Tok == comment)
                {
                    Comment;
                    Tok = whitespace;
                }
            }
            break;
        case ident:
            if (Ch.isAlphaNum)
            {
                GetPos;
                Tok = Node[Ch].Tok;
                GetCh;
            }
            else
            {
                mode = none;
                Get(Tok);
            }
            break;
        case string_:
            if (Ch == eot)
            {
                Tok = eot;
            }
            else
            {
                if (Ch == StringCh || Ch == eol)
                    mode = none;
                GetPos;
                Tok = Node[Ch].Tok;
                GetCh;
            }
            break;
    }
}

void Comment()
{
    int Level = 1;

    while (true)
    {
        if (Ch == eot)
        {
            error!"comment not closed\n%s"(Pos);
            break;
        }
        else if (Ch == '(')
        {
            GetCh;
            if (Ch == '*')
            {
                GetCh;
                ++Level;
            }
        }
        else if (Ch == '*')
        {
            GetCh;
            if (Ch == ')')
            {
                GetCh;
                --Level;
                if (Level == 0)
                    break;
            }
        }
        else
        {
            GetCh;
        }
    }
}

void Keyword(ref int Tok)
{
    int Ptr = Ch;

    if (Ptr !in Node)
    {
        Tok = undef;
        GetCh;
        return;
    }
    Tok = Node[Ptr].Tok;
    if (NextCh >= ChBuf.length - maxTokLen)
        CopyBuf;

    int Mark = CurCh;
    int LastPtr;

    do
    {
        LastPtr = Ptr;
        Ptr = Node[Ptr].Sub;
        GetBufCh;
        while (Ptr != nil && Node[Ptr].Ch != Ch)
            Ptr = Node[Ptr].Next;
    }
    while (Ptr != nil);
    if (Node[LastPtr].Tok != undef && !Ch.isAlphaNum)
    {
        Tok = Node[LastPtr].Tok;
        CurCh = NextCh - 1;
    }
    else
    {
        CurCh = Mark;
        mode = Mode.ident;
    }
    GetCh;
}

void Symbol(ref int Tok)
{
    int Ptr = Ch;

    Tok = Node[Ptr].Tok;
    if (Node[Ptr].Sub != nil)
    {
        if (NextCh >= ChBuf.length - maxTokLen)
            CopyBuf;

        int Mark = CurCh;

        do
        {
            if (Node[Ptr].Tok != undef)
            {
                Tok = Node[Ptr].Tok;
                Mark = CurCh;
            }
            Ptr = Node[Ptr].Sub;
            GetBufCh;
            while (Ptr != nil && Node[Ptr].Ch != Ch)
                Ptr = Node[Ptr].Next;
        }
        while (Ptr != nil);
        CurCh = Mark;
    }
    GetCh;
}

void CopyBuf()
{
    int i = CurCh;
    int j = firstChBuf;

    while (i < NextCh)
    {
        ChBuf[j] = ChBuf[i];
        PosBuf[j] = PosBuf[i];
        ++i;
        ++j;
    }
    CurCh = firstChBuf;
    NextCh = j;
}

void GetCh()
{
    if (CurCh == NextCh)
    {
        Read(In, Ch);
    }
    else
    {
        Ch = ChBuf[CurCh];
        ++CurCh;
    }
}

void GetBufCh()
{
    if (CurCh == NextCh)
    {
        PosBuf[NextCh] = In.position;
        Read(In, Ch);
        ChBuf[NextCh] = Ch;
        ++NextCh;
        ++CurCh;
    }
    else
    {
        Ch = ChBuf[CurCh];
        ++CurCh;
    }
}

void GetPos()
{
    if (CurCh == NextCh)
        Pos = PrevPos;
    else
        Pos = PosBuf[CurCh - 1];
}

string Repr(int Tok)
{
    import std.string : fromStringz;

    return fromStringz(NameTab[Tok].ptr).idup;
}

void Init(Input input)
{
    In = input;
    CurCh = firstChBuf;
    NextCh = firstChBuf;
    Ch = ' ';
    mode = Mode.none;
    Get = &Get2;
}

struct NodeRecord
{
    dchar Ch;
    int Tok = undef;
    int Next = nil;
    int Sub = nil;
}

NodeRecord[dchar] Node;

int NextNode;
char[maxTokLen][maxTok] NameTab;

static this()
{
    BuildTree;
}

void BuildTree()
{
    import std.conv : to;

    NextNode = '~' + 1;
    for (int i = firstNode; i <= NextNode; ++i)
        Node[i] = NodeRecord(i);
    ++NextNode;
    COPY("endTok", NameTab[0]);
    COPY("undefTok", NameTab[1]);
    COPY("sepTok", NameTab[2]);
    Enter(whitespace, eol.to!string);
    Enter(comment, "(*");
$
}

private void COPY(T)(string x, ref T v)
{
    import std.algorithm : copy, fill;

    fill(v[], '\0');
    copy(x[], v[]);
}

void Enter(int Tok, string Name)
{
    import std.range : empty, front, popFront;

    int Ptr;

    void Insert(ref int Ptr, dchar Ch)
    {
        Ptr = NextNode;
        Node[NextNode] = NodeRecord(Ch);
        ++NextNode;
    }

    if (Tok >= 0)
        COPY(Name, NameTab[Tok]);
    Ptr = Name.front;
    while (!Name.empty)
    {
        if (Ptr !in Node)
            Node[Ptr] = NodeRecord(Ptr);
        while (Node[Ptr].Ch != Name.front && Node[Ptr].Next != nil)
            Ptr = Node[Ptr].Next;
        if (Node[Ptr].Ch != Name.front)
        {
            Insert(Node[Ptr].Next, Name.front);
            Ptr = Node[Ptr].Next;
        }
        Name.popFront;
        if (Node[Ptr].Sub != nil && !Name.empty)
        {
            Ptr = Node[Ptr].Sub;
        }
        else
        {
            while (!Name.empty)
            {
                Insert(Node[Ptr].Sub, Name.front);
                Ptr = Node[Ptr].Sub;
                Name.popFront;
            }
        }
    }
    Node[Ptr].Tok = Tok;
}

private void Read(ref Input input, ref dchar c)
{
    c = input.front;
    PrevPos = input.position;
    if (!input.empty)
        input.popFront;
}

// END $.
$

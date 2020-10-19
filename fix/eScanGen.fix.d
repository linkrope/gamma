module $;

import IO = eIO;
import io : Input, Position;
import runtime;
import std.stdio;

const eot = 0;
const eol = '\n';
const firstChBuf = 0;
const chBufLen = 512;
char[chBufLen] ChBuf;
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
const string_ = 0;
const ident = 1;
const none = 2;

struct NodeRecord
{
    char Ch;
    int Tok;
    int Next;
    int Sub;
}

alias OpenNode = NodeRecord[];
OpenNode Node;

int NextNode;
char[maxTokLen][maxTok] NameTab;
bool[256] IsWhitespace;
bool[256] IsIdent;
char Ch;
int Mode;
char StringCh;
Position Pos;
Position PrevPos;

void function(ref int Tok) Get;

void CopyBuf()
{
    int i;
    int j;
    i = CurCh;
    j = firstChBuf;
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
    {
        Pos = PrevPos;
    }
    else
    {
        Pos = PosBuf[CurCh - 1];
    }
}

void Enter(int Tok, string Name)
{
    int Ptr;
    int i;

    void Insert(ref int Ptr, char Ch)
    {
        void Expand()
        {
            long i;
            OpenNode Node1;

            if (NextNode >= Node.length)
            {
                if (Node.length < DIV(int.max, 2))
                {
                    Node1 = new NodeRecord[2 * Node.length + 1];
                    for (i = firstNode; i < Node.length; ++i)
                        Node1[i] = Node[i];
                    Node = Node1;
                }
                else
                {
                    assert(0);
                }
            }
        }

        Ptr = NextNode;
        Node[NextNode].Ch = Ch;
        Node[NextNode].Tok = undef;
        Node[NextNode].Next = nil;
        Node[NextNode].Sub = nil;
        ++NextNode;
        if (NextNode >= Node.length)
        {
            Expand;
        }
    }

    if (Tok >= 0)
    {
        COPY(Name, NameTab[Tok]);
    }
    Ptr = Name[0];
    i = 0;
    while (i < Name.length)
    {
        while (Node[Ptr].Ch != Name[i] && Node[Ptr].Next != nil)
        {
            Ptr = Node[Ptr].Next;
        }
        if (Node[Ptr].Ch != Name[i])
        {
            Insert(Node[Ptr].Next, Name[i]);
            Ptr = Node[Ptr].Next;
        }
        ++i;
        if (Node[Ptr].Sub != nil && i < Name.length)
        {
            Ptr = Node[Ptr].Sub;
        }
        else
        {
            while (i < Name.length)
            {
                Insert(Node[Ptr].Sub, Name[i]);
                Ptr = Node[Ptr].Sub;
                ++i;
            }
        }
    }
    Node[Ptr].Tok = Tok;
}

void WriteRepr(ref IO.TextOut Out, int Tok)
{
    Out.write(NameTab[Tok]);
}

void Symbol(ref int Tok)
{
    int Ptr = Ch;
    int Mark;

    Tok = Node[Ptr].Tok;
    if (Node[Ptr].Sub != nil)
    {
        if (NextCh >= ChBuf.length - maxTokLen)
        {
            CopyBuf;
        }
        Mark = CurCh;
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
            {
                Ptr = Node[Ptr].Next;
            }
        }
        while (!(Ptr == nil));
        CurCh = Mark;
    }
    GetCh;
}

void Keyword(ref int Tok)
{
    int Ptr = Ch;
    int LastPtr;
    int Mark;

    Tok = Node[Ptr].Tok;
    if (NextCh >= ChBuf.length - maxTokLen)
    {
        CopyBuf;
    }
    Mark = CurCh;
    do
    {
        LastPtr = Ptr;
        Ptr = Node[Ptr].Sub;
        GetBufCh;
        while (Ptr != nil && Node[Ptr].Ch != Ch)
        {
            Ptr = Node[Ptr].Next;
        }
    }
    while (!(Ptr == nil));
    if (Node[LastPtr].Tok != undef && !IsIdent[Ch])
    {
        Tok = Node[LastPtr].Tok;
        CurCh = NextCh - 1;
    }
    else
    {
        CurCh = Mark;
        Mode = ident;
    }
    GetCh;
}

void Comment()
{
    void Error(string Txt)
    {
        writeln;
        writeln(Pos);
        IO.Msg.write("  ");
        IO.Msg.write(Txt);
        IO.Msg.writeln;
        IO.Msg.flush;
    }

    int Level = 1;

    while (true)
    {
        if (Ch == eot)
        {
            Error("Comment not closed");
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
                {
                    break;
                }
            }
        }
        else
        {
            GetCh;
        }
    }
}

void Get2(ref int Tok)
{
    switch (Mode)
    {
    case string_:
        if (Ch == eot)
        {
            Tok = eot;
        }
        else
        {
            if (Ch == StringCh || Ch == eol)
            {
                Mode = none;
            }
            GetPos;
            Tok = Node[Ch].Tok;
            GetCh;
        }
        break;
    case ident:
        if (IsIdent[Ch])
        {
            GetPos;
            Tok = Node[Ch].Tok;
            GetCh;
        }
        else
        {
            Mode = none;
            Get(Tok);
        }
        break;
    default:
        while (IsWhitespace[Ch])
        {
            GetCh;
        }
        GetPos;
        if (Ch == eot)
        {
            Tok = eot;
        }
        else if (IsIdent[Ch])
        {
            Keyword(Tok);
        }
        else if (Ch == '"' || Ch == '\'')
        {
            StringCh = Ch;
            Mode = string_;
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
    }
}

void Get3(ref int Tok)
{
    switch (Mode)
    {
    case string_:
        if (Ch == eot)
        {
            Tok = eot;
        }
        else
        {
            if (Ch == StringCh || Ch == eol)
            {
                Mode = none;
            }
            GetPos;
            Tok = Node[Ch].Tok;
            GetCh;
        }
        break;
    case ident:
        if (IsIdent[Ch])
        {
            GetPos;
            Tok = Node[Ch].Tok;
            GetCh;
        }
        else
        {
            Mode = none;
            Get(Tok);
        }
        break;
    default:
        GetPos;
        if (Ch == eot)
        {
            Tok = eot;
        }
        else if (IsWhitespace[Ch])
        {
            do
            {
                GetCh;
            }
            while (!!IsWhitespace[Ch]);
            Tok = whitespace;
        }
        else if (IsIdent[Ch])
        {
            Keyword(Tok);
        }
        else if (Ch == '"' || Ch == '\'')
        {
            StringCh = Ch;
            Mode = string_;
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
    }
}

void Init(Input input)
{
    In = input;
    CurCh = firstChBuf;
    NextCh = firstChBuf;
    Ch = ' ';
    Mode = none;
    Get = &Get2;
}

void BuildTree()
{
    import std.conv : to;

    for (int i = 0; i < IsIdent.length; ++i)
    {
        if ('A' <= i && i <= 'Z')
            IsIdent[i] = true;
        else if ('a' <= i  && i <= 'z')
            IsIdent[i] = true;
        else if ('0' <= i  && i <= '9')
            IsIdent[i] = true;
        else
            IsIdent[i] = false;
    }
    for (int i = 0; i < IsWhitespace.length; ++i)
    {
        if (i <= ' ' || '~' < i)
            IsWhitespace[i] = true;
        else
            IsWhitespace[i] = false;
    }
    IsWhitespace[eot] = false;
    Node = new NodeRecord[255];
    NextNode = '~' + 1;
    for (int i = firstNode; i <= NextNode; ++i)
    {
        Node[i].Ch = i.to!char;
        Node[i].Tok = undef;
        Node[i].Next = nil;
        Node[i].Sub = nil;
    }
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

private void Read(ref Input input, ref char c)
{
    import std.conv : to;

    c = input.front.to!char;
    PrevPos = input.position;
    if (!input.empty)
        input.popFront;
}

static this()
{
    BuildTree;
}

// END $.
$

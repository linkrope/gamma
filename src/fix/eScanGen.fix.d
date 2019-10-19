module $;
import runtime;
import IO = eIO;

const EOT = '\x00';
const firstChBuf = 0;
const chBufLen = 512;
char[chBufLen] ChBuf;
IO.Position[chBufLen] PosBuf;
int CurCh;
int NextCh;
IO.TextIn In;
const nil = 0;
const firstNode = 1;
const maxTokLen = $;
const maxTok = $;
const eot = 0;
const undef = 1;
const whitespace = 2;
const comment = int.min;
const string = 0;
const ident = 1;
const none = 2;
// TODO OpenNode = POINTER TO ARRAY OF RECORD Ch: CHAR; Tok, Next, Sub: INTEGER END;
OpenNode Node;
int NextNode;
char[maxTokLen][maxTok] NameTab;
bool[256] IsWhitespace;
bool[256] IsIdent;
char Ch;
int Mode;
char StringCh;
IO.Position Pos;
// TODO: Get*: PROCEDURE (VAR Tok: INTEGER);

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
        IO.Read(In, Ch);
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
        IO.Pos(In, PosBuf[NextCh]);
        IO.Read(In, Ch);
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
        IO.PrevPos(In, Pos);
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
                    NEW(Node1, 2 * Node.length + 1);
                    for (i = firstNode; i <= Node.length - 1; ++i)
                    {
                        Node1[i] = Node[i];
                    }
                    Node = Node1;
                }
                else
                {
                    HALT(99);
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
    Ptr = ORD(Name[0]);
    i = 0;
    while (Name[i] != '\x00')
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
        if (Node[Ptr].Sub != nil && Name[i] != '\x00')
        {
            Ptr = Node[Ptr].Sub;
        }
        else
        {
            while (i < Name.length - 1)
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
    IO.WriteString(Out, NameTab[Tok]);
}

void Symbol(ref int Tok)
{
    int Ptr;
    int Mark;
    Ptr = ORD(Ch);
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
    int Ptr;
    int LastPtr;
    int Mark;
    Ptr = ORD(Ch);
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
    if (Node[LastPtr].Tok != undef && !IsIdent[ORD(Ch)])
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
    int Level;

    void Error(string Txt)
    {
        IO.WritePos(IO.Msg, Pos);
        IO.WriteString(IO.Msg, "  ");
        IO.WriteString(IO.Msg, Txt);
        IO.WriteLn(IO.Msg);
        IO.Update(IO.Msg);
    }

    Level = 1;
    while (true)
    {
        if (Ch == EOT)
        {
            Error("Comment not closed");
            break;
        }
        else if (Ch == "(")
        {
            GetCh;
            if (Ch == "*")
            {
                GetCh;
                ++Level;
            }
        }
        else if (Ch == "*")
        {
            GetCh;
            if (Ch == ")")
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
    case string:
        if (Ch == EOT)
        {
            Tok = eot;
        }
        else
        {
            if (Ch == StringCh || Ch == IO.eol)
            {
                Mode = none;
            }
            GetPos;
            Tok = Node[ORD(Ch)].Tok;
            GetCh;
        }
        break;
    case ident:
        if (IsIdent[ORD(Ch)])
        {
            GetPos;
            Tok = Node[ORD(Ch)].Tok;
            GetCh;
        }
        else
        {
            Mode = none;
            Get(Tok);
        }
        break;
    default:
        while (IsWhitespace[ORD(Ch)])
        {
            GetCh;
        }
        GetPos;
        if (Ch == EOT)
        {
            Tok = eot;
        }
        else if (IsIdent[ORD(Ch)])
        {
            Keyword(Tok);
        }
        else if (Ch == "\"" || Ch == "'")
        {
            StringCh = Ch;
            Mode = string;
            Tok = Node[ORD(Ch)].Tok;
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
    case string:
        if (Ch == EOT)
        {
            Tok = eot;
        }
        else
        {
            if (Ch == StringCh || Ch == IO.eol)
            {
                Mode = none;
            }
            GetPos;
            Tok = Node[ORD(Ch)].Tok;
            GetCh;
        }
        break;
    case ident:
        if (IsIdent[ORD(Ch)])
        {
            GetPos;
            Tok = Node[ORD(Ch)].Tok;
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
        if (Ch == EOT)
        {
            Tok = eot;
        }
        else if (IsWhitespace[ORD(Ch)])
        {
            do
            {
                GetCh;
            }
            while (!!IsWhitespace[ORD(Ch)]);
            Tok = whitespace;
        }
        else if (IsIdent[ORD(Ch)])
        {
            Keyword(Tok);
        }
        else if (Ch == "\"" || Ch == "'")
        {
            StringCh = Ch;
            Mode = string;
            Tok = Node[ORD(Ch)].Tok;
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

void Init()
{
    char[512] Name;
    bool Error;
    IO.InputName(Name);
    IO.OpenIn(In, Name, Error);
    if (Error)
    {
        IO.WriteText(IO.Msg, "error: cannot open input\n");
        IO.Update(IO.Msg);
        HALT(99);
    }
    CurCh = firstChBuf;
    NextCh = firstChBuf;
    Ch = " ";
    Mode = none;
    Get = Get2;
}

void BuildTree()
{
    int i;
    for (i = 0; i <= IsIdent.length - 1; ++i)
    {
        if (CHR(i) >= "A" && CHR(i) <= "Z")
        {
            IsIdent[i] = true;
        }
        else if (CHR(i) >= "a" && CHR(i) <= "z")
        {
            IsIdent[i] = true;
        }
        else if (CHR(i) >= "0" && CHR(i) <= "9")
        {
            IsIdent[i] = true;
        }
        else
        {
            IsIdent[i] = false;
        }
    }
    for (i = 0; i <= IsWhitespace.length - 1; ++i)
    {
        if (CHR(i) <= " " || CHR(i) > "~")
        {
            IsWhitespace[i] = true;
        }
        else
        {
            IsWhitespace[i] = false;
        }
    }
    IsWhitespace[ORD(EOT)] = false;
    NEW(Node, 255);
    NextNode = ORD("~") + 1;
    for (i = firstNode; i <= NextNode; ++i)
    {
        Node[i].Ch = CHR(i);
        Node[i].Tok = undef;
        Node[i].Next = nil;
        Node[i].Sub = nil;
    }
    ++NextNode;
    COPY("endTok", NameTab[0]);
    COPY("undefTok", NameTab[1]);
    COPY("sepTok", NameTab[2]);
    Enter(whitespace, IO.eol);
    Enter(comment, "(*");
    $
}

static this()
{
    BuildTree;
}

$

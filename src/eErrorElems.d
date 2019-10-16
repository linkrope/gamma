module eErrorElems;
import runtime;
import Viewers;
import Input;
import Display;
import Fonts;
import Texts;
import Oberon;
import TextFrames;
import TextPrinter;

const eol = '\x0d';
const tab = '\x09';
const syntax = 0;
const restart = 1;
const insert = 2;
const semantic = 3;
const syntaxSym = " S ";
const restartSym = " > ";
const insertSym = " i ";
const semanticSym = " ? ";
const syntaxTxt = " exp  ";
const restartTxt = " restart ";
const insertTxt = " ins  ";
const maxErrStringLen = 180;
const maxErrorElems = 1000;
alias Elem = ElemDesc;
class ElemDesc : Texts.ElemDesc
{
    short id;
    bool Collapsed;
    char[maxErrStringLen] ErrString;
    char[4] ErrSym;
}

Texts.Writer W;
Texts.Notifier OrigNotifier;
long StrDispWidth(Fonts.Font fnt, char[] s)
{
    Display.Pattern pat;
    int width;
    int i;
    int dx;
    int x;
    int y;
    int w;
    int h;
    char ch;
    width = 0;
    i = 0;
    ch = s[i];
    while (ch != '\x00')
    {
        Display.GetChar(fnt.raster, ch, dx, x, y, w, h, pat);
        INC(width, dx);
        ++i;
        ch = s[i];
    }
    return LONG(width) * TextFrames.Unit;
}

void DispStr(Fonts.Font fnt, char[] s, int col, int x0, int y0)
{
    Display.Pattern pat;
    int i;
    int dx;
    int x;
    int y;
    int w;
    int h;
    char ch;
    i = 0;
    ch = s[i];
    while (ch != '\x00')
    {
        Display.GetChar(fnt.raster, ch, dx, x, y, w, h, pat);
        Display.CopyPattern(col, pat, x0 + x, y0 + y, Display.replace);
        ++i;
        ch = s[i];
        INC(x0, dx);
    }
}

void Open(Elem e, short id, char[] s, bool clpsd)
{
    e.W = 5 * TextFrames.mm;
    e.H = e.W;
    e.handle = Handle;
    e.id = id;
    COPY(s, e.ErrString);
    e.Collapsed = clpsd;
    switch (id)
    {
    case syntax:
        e.ErrSym = syntaxSym;
        break;
    case restart:
        e.ErrSym = restartSym;
        break;
    case insert:
        e.ErrSym = insertSym;
        break;
    case semantic:
        e.ErrSym = semanticSym;
        break;
    }
}

void Copy(Elem se, Elem de)
{
    Texts.CopyElem(se, de);
    de.ErrString = se.ErrString;
    de.id = se.id;
    de.Collapsed = se.Collapsed;
    de.ErrSym = se.ErrSym;
}

void Changed(Elem e, long pos)
{
    Texts.Text T;
    T = Texts.ElemBase(e);
    T.notify(T, Texts.replace, pos, pos + 1);
}

void PrepDraw(Elem e, Fonts.Font fnt, ref int dy)
{
    if (e.Collapsed)
    {
        e.W = StrDispWidth(fnt, e.ErrSym);
    }
    else
    {
        e.W = StrDispWidth(fnt, e.ErrString);
    }
    e.H = LONG(fnt.height) * TextFrames.Unit;
    dy = fnt.minY;
}

void Draw(Elem e, long pos, Fonts.Font fnt, int col, int x0, int y0)
{
    TextFrames.Parc p;
    long beg;
    int y;
    int w;
    int h;
    w = SHORT(DIV(e.W, TextFrames.Unit));
    h = SHORT(DIV(e.H, TextFrames.Unit));
    TextFrames.ParcBefore(Texts.ElemBase(e), pos, p, beg);
    y = y0 + SHORT(DIV(p.dsr, TextFrames.Unit));
    if (e.Collapsed)
    {
        DispStr(fnt, e.ErrSym, col, x0, y);
    }
    else
    {
        DispStr(fnt, e.ErrString, col, x0, y);
    }
    Display.ReplConst(Display.white, x0 + 1, y + fnt.minY, w - 2, h, Display.invert);
}

void PrepPrint(Elem e, Fonts.Font fnt, ref int dy)
{
    e.W = 0;
    e.H = 0;
}

void Print(Elem e, long pos, Fonts.Font fnt, int x0, int y0)
{
    TextFrames.Parc p;
    long beg;
    int w;
    if (e.Collapsed)
    {
        e.W = StrDispWidth(fnt, e.ErrSym);
    }
    else
    {
        e.W = StrDispWidth(fnt, e.ErrString);
    }
    e.H = LONG(fnt.height) * TextFrames.Unit;
}

void Track(Elem e, long pos, int x, int y, uint keys)
{
    uint keysum;
    if (keys == Set)
    {
        keysum = keys;
        do
        {
            Oberon.DrawCursor(Oberon.Mouse, Oberon.Arrow, x, y);
            Input.Mouse(keys, x, y);
            keysum = keysum + keys;
        }
        while (!(keys == Set));
        if (keysum == Set)
        {
            e.Collapsed = !e.Collapsed;
            Changed(e, pos);
        }
    }
}

void Handle(Texts.Elem e, ref Texts.ElemMsg msg)
{
    Elem copy;
    // TODO WITH e : Elem DO
    if (msg is Texts.CopyMsg)
    {
        NEW(copy);
        Copy(e, copy);
        msg(Texts.CopyMsg).e = copy;
    }
    else if (msg is TextFrames.DisplayMsg)
    {
        // TODO WITH msg : TextFrames.DisplayMsg DO
        if (msg.prepare)
        {
            PrepDraw(e, msg.fnt, msg.Y0);
        }
        else
        {
            Draw(e, msg.pos, msg.fnt, msg.col, msg.X0, msg.Y0);
        }
    }
    else if (msg is TextPrinter.PrintMsg)
    {
        // TODO WITH msg : TextPrinter.PrintMsg DO
        if (msg.prepare)
        {
            PrepPrint(e, msg.fnt, msg.Y0);
        }
        else
        {
            Print(e, msg.pos, msg.fnt, msg.X0, msg.Y0);
        }
    }
    else if (msg is TextFrames.TrackMsg)
    {
        // TODO WITH msg : TextFrames.TrackMsg DO
        Track(e, msg.pos, msg.X, msg.Y, msg.keys);
    }
}

void DummyNotifier(Texts.Text T, int op, long beg, long end)
{
}

void DisableNotifier(ref Texts.Text T)
{
    OrigNotifier = T.notify;
    T.notify = DummyNotifier;
}

void EnableNotifier(ref Texts.Text T)
{
    T.notify = OrigNotifier;
    T.notify(T, Texts.replace, 0, T.len);
}

Texts.Text MarkedText()
{
    Viewers.Viewer V;
    V = Oberon.MarkedViewer();
    if (V.dsc != null && V.dsc.next != null && V.dsc.next is TextFrames.Frame)
    {
        return V.dsc.next(TextFrames.Frame).text;
    }
    else
    {
        return null;
    }
}

void Insert()
{
    Texts.Scanner S;
    Texts.Reader ElemR;
    Texts.Text sT;
    Texts.Text dT;
    long scanPos;
    long Beg;
    long End;
    long Time;
    long ErrPos;
    char[maxErrStringLen] Str;
    int NextCh;
    long[maxErrorElems] Position;
    int NextPosition;
    void Put(Texts.Text T, long pos, short id, ref char[] s)
    {
        Elem e;
        long Offset;
        int i;
        Offset = 0;
        for (i = 0; i <= NextPosition - 1; ++i)
        {
            if (pos >= Position[i])
            {
                ++Offset;
            }
        }
        Position[NextPosition] = pos;
        ++NextPosition;
        if (pos + Offset <= T.len)
        {
            NEW(e);
            Open(e, id, s, true);
            Texts.WriteElem(W, e);
            Texts.Insert(T, pos + Offset, W.buf);
        }
    }

    sT = Oberon.Par.text;
    Texts.OpenScanner(S, sT, Oberon.Par.pos);
    Texts.Scan(S);
    if (S.class_ == Texts.Char && (S.c == "^" || S.c == "@"))
    {
        Oberon.GetSelection(sT, Beg, End, Time);
        if (Time >= 0)
        {
            Texts.OpenScanner(S, sT, Beg);
            Texts.Scan(S);
        }
        else
        {
            return;
        }
    }
    dT = MarkedText();
    if (dT == null || sT == dT)
    {
        return;
    }
    Texts.OpenReader(ElemR, dT, 0);
    do
    {
        Texts.ReadElem(ElemR);
    }
    while (!(ElemR.eot || ElemR.elem == null || ElemR.elem is Elem));
    if (ElemR.elem != null)
    {
        return;
    }
    DisableNotifier(dT);
    NextPosition = 0;
    while (true)
    {
        if (NextPosition >= maxErrorElems)
        {
            break;
        }
        if (S.class_ != Texts.Name || S.s != "pos")
        {
            break;
        }
        Texts.Scan(S);
        if (S.class_ == Texts.Int)
        {
            ErrPos = S.i;
        }
        else
        {
            break;
        }
        scanPos = Texts.Pos(S) - 1;
        Texts.Scan(S);
        if (S.class_ == Texts.Name && S.s == "syntax")
        {
            COPY(syntaxTxt, Str);
            NextCh = 0;
            while (Str[NextCh] != '\x00')
            {
                ++NextCh;
            }
            while (!S.eot && S.nextCh != ":")
            {
                Texts.Read(S, S.nextCh);
            }
            Texts.Read(S, S.nextCh);
            while (!S.eot && S.nextCh != eol)
            {
                if (NextCh < Str.length - 2)
                {
                    Str[NextCh] = S.nextCh;
                    ++NextCh;
                }
                Texts.Read(S, S.nextCh);
            }
            Str[NextCh] = " ";
            Str[NextCh + 1] = '\x00';
            Put(dT, ErrPos, syntax, Str);
            Texts.Scan(S);
        }
        else if (S.class_ == Texts.Name && S.s == "restart")
        {
            COPY(restartTxt, Str);
            Put(dT, ErrPos, restart, Str);
            while (!S.eot && S.nextCh != eol)
            {
                Texts.Read(S, S.nextCh);
            }
            Texts.Scan(S);
        }
        else if (S.class_ == Texts.Name && S.s == "symbol")
        {
            COPY(insertTxt, Str);
            NextCh = 0;
            while (Str[NextCh] != '\x00')
            {
                ++NextCh;
            }
            while (!S.eot && S.nextCh != ":")
            {
                Texts.Read(S, S.nextCh);
            }
            Texts.Read(S, S.nextCh);
            while (!S.eot && S.nextCh != eol)
            {
                if (NextCh < Str.length - 2)
                {
                    Str[NextCh] = S.nextCh;
                    ++NextCh;
                }
                Texts.Read(S, S.nextCh);
            }
            Str[NextCh] = " ";
            Str[NextCh + 1] = '\x00';
            Put(dT, ErrPos, insert, Str);
            Texts.Scan(S);
        }
        else
        {
            Texts.OpenScanner(S, sT, scanPos);
            Str[0] = " ";
            NextCh = 1;
            while (S.nextCh == " " || S.nextCh == tab)
            {
                Texts.Read(S, S.nextCh);
            }
            while (!S.eot && S.nextCh != eol)
            {
                if (NextCh < Str.length - 2)
                {
                    Str[NextCh] = S.nextCh;
                    ++NextCh;
                }
                Texts.Read(S, S.nextCh);
            }
            Str[NextCh] = " ";
            Str[NextCh + 1] = '\x00';
            Put(dT, ErrPos, semantic, Str);
            Texts.Scan(S);
        }
    }
    EnableNotifier(dT);
}

void Remove()
{
    Texts.Text T;
    Texts.Reader R;
    long Pos;
    T = MarkedText();
    if (T == null)
    {
        return;
    }
    Texts.OpenReader(R, T, 0);
    DisableNotifier(T);
    while (true)
    {
        Texts.ReadElem(R);
        if (R.eot || R.elem == null)
        {
            break;
        }
        if (R.elem is Elem)
        {
            Pos = Texts.ElemPos(R.elem);
            Texts.Delete(T, Pos, Pos + 1);
            Texts.OpenReader(R, T, Pos);
        }
    }
    EnableNotifier(T);
}

void Repair()
{
    Texts.Text T;
    Texts.Reader R;
    long Beg;
    long End;
    int i;
    T = MarkedText();
    if (T == null)
    {
        return;
    }
    Texts.OpenReader(R, T, 0);
    Beg = 0;
    DisableNotifier(T);
    while (true)
    {
        Texts.ReadElem(R);
        if (R.eot || R.elem == null)
        {
            break;
        }
        if (R.elem is Elem)
        {
            if (R.elem(Elem).id == syntax)
            {
                Beg = Texts.ElemPos(R.elem);
                Texts.Delete(T, Beg, Beg + 1);
            }
            else if (R.elem(Elem).id == restart)
            {
                End = Texts.ElemPos(R.elem);
                Texts.Delete(T, Beg, End + 1);
            }
            else if (R.elem(Elem).id == insert)
            {
                i = 0;
                while (i < 6 && R.elem(Elem).ErrString[i] != '\x00')
                {
                    ++i;
                }
                while (R.elem(Elem).ErrString[i] != '\x00')
                {
                    Texts.Write(W, R.elem(Elem).ErrString[i]);
                    ++i;
                }
                End = Texts.ElemPos(R.elem);
                Texts.Delete(T, End, End + 1);
                Texts.Insert(T, End, W.buf);
            }
            else
            {
                End = Texts.ElemPos(R.elem);
                Texts.Delete(T, End, End + 1);
            }
        }
    }
    EnableNotifier(T);
}

void Next()
{
    Viewers.Viewer V;
    TextFrames.Frame F;
    Texts.Reader R;
    long pos;
    void Show(TextFrames.Frame F, long pos)
    {
        long beg;
        long end;
        long delta;
        if (pos >= 200)
        {
            delta = 200;
        }
        else
        {
            delta = pos;
        }
        while (true)
        {
            beg = F.org;
            end = TextFrames.Pos(F, F.X, F.Y);
            if (beg <= pos && pos < end || beg == end)
            {
                break;
            }
            TextFrames.Show(F, pos - delta);
            DEC(delta, 20);
            if (delta < 0)
            {
                delta = 0;
            }
        }
    }

    V = Oberon.MarkedViewer();
    if (V.dsc != null && V.dsc.next != null && V.dsc.next is TextFrames.Frame)
    {
        F = V.dsc.next(TextFrames.Frame);
    }
    else
    {
        return;
    }
    if (F.hasCar)
    {
        pos = F.carloc.pos;
    }
    else
    {
        pos = 0;
    }
    Texts.OpenReader(R, F.text, pos);
    do
    {
        Texts.ReadElem(R);
    }
    while (!(R.eot || R.elem == null || R.elem is Elem));
    if (!R.eot && R.elem != null && R.elem is Elem)
    {
        Oberon.PassFocus(Viewers.This(F.X, F.Y));
        pos = Texts.ElemPos(R.elem);
        Show(F, pos);
        TextFrames.SetCaret(F, pos + 1);
    }
    else
    {
        TextFrames.RemoveCaret(F);
    }
}

static this()
{
    Texts.OpenWriter(W);
}

module epsilon.analyzer;

import EAG = epsilon.eag;
import Earley = epsilon.earley;
import epsilon.lexer : Lexer, Token;
import io : Input, Position;
import log;
import runtime;
import std.bitmanip : BitArray;
import std.conv : to;

const nil = EAG.nil;
int ErrorCounter;
bool NameNotified;

Lexer lexer;

void Error(Position Pos, string ErrMsg) @safe
{
    import std.exception : enforce;

    ++ErrorCounter;

    enforce(ErrorCounter <= 25,
            "Too many errors!");

    error!"%s\n%s"(ErrMsg, Pos);
}

/**
 * Specification:
 *   (MetaRule | HyperRule) {MetaRule | HyperRule} .
 */
void Specification()
{
    /**
     * MetaRule:
     *   ident "=" MetaExpr ".".
     */
    void MetaRule(int Id, bool IsToken)
    {
        const MNont = EAG.FindMNont(Id);

        /**
         * MetaExpr:
         *   MetaTerm {"|" MetaTerm}.
         */
        void MetaExpr()
        {
            /**
             * MetaTerm:
             *   {ident | string}.
             */
            void MetaTerm()
            {
                while (true)
                {
                    if (lexer.front == Token.name)
                    {
                        EAG.AppMemb(EAG.FindMNont(lexer.value.to!int));
                        lexer.popFront;
                        if (lexer.front == Token.number)
                        {
                            Error(lexer.position, "number is not allowed here");
                            lexer.popFront;
                        }
                    }
                    else if (lexer.front == Token.string_)
                    {
                        EAG.AppMemb(-EAG.FindMTerm(lexer.value.to!int));
                        lexer.popFront;
                    }
                    else
                    {
                        EAG.AppMemb(EAG.nil);
                        break;
                    }
                }
            }

            while (true)
            {
                const Rhs = EAG.NextMemb;

                MetaTerm;
                EAG.AppMemb(EAG.NewMAlt(MNont, Rhs));
                if (lexer.front == '|')
                    lexer.popFront;
                else
                    break;
            }
        }

        EAG.MNont[MNont].IsToken = EAG.MNont[MNont].IsToken || IsToken;
        if (lexer.front == '=')
            lexer.popFront;
        else
            Error(lexer.position, "'=' expected");
        MetaExpr;
        if (lexer.front == '.')
            lexer.popFront;
        else
            Error(lexer.position, "'.' expected");
    }

    void SetBaseName()
    {
        EAG.StartSym = EAG.firstHNont;
        EAG.BaseName = EAG.symbolTable.symbol(EAG.HNont[EAG.StartSym].Id);
    }

    /**
     * HyperRule:
     *   ident [FormalParams] ":" HyperExpr ".".
     */
    void HyperRule(int Id, bool IsToken)
    {
        void Distribute(int Sym, EAG.Alt A, int Sig, EAG.ParamsDesc Formal)
        {
            void CopyParams(ref int s, ref int d)
            {
                int Affixform;
                int P = s;

                d = EAG.NextParam;
                while (EAG.ParamBuf[P].Affixform != nil)
                {
                    Earley.CopyAffixform(EAG.ParamBuf[P].Affixform, Affixform);
                    EAG.AppParam(Affixform, EAG.ParamBuf[P].Pos);
                    ++P;
                }
                EAG.AppParam(nil, EAG.ParamBuf[P].Pos);
            }

            EAG.HNont[Sym].Sig = Sig;
            A.Formal.Pos = Formal.Pos;
            A.Formal.Params = Formal.Params;
            A = A.Next;
            while (A !is null)
            {
                A.Formal.Pos = Formal.Pos;
                CopyParams(Formal.Params, A.Formal.Params);
                A = A.Next;
            }
        }

        /**
         * FormalParams:
         *   "<" ("+" | "-") Affixform ":" ident {"," ("+" | "-") Affixform ":" ident} ">".
         * ActualParams:
         *   "<" Affixform {"," Affixform} ">".
         */
        void Params(ref EAG.ParamsDesc Actual, ref EAG.ParamsDesc Formal)
        {
            /**
             * Affixform:
             *   {string | ["!"] ident [number]}.
             */
            void Affixform(ref int Sym)
            {
                int Cnt = 0;

                while (true)
                {
                    short Uneq;
                    int Num;
                    Position Pos = lexer.position;

                    if (lexer.front == Token.string_)
                    {
                        Sym = -EAG.FindMTerm(lexer.value.to!int);
                        Num = 0;
                        lexer.popFront;
                        ++Cnt;
                    }
                    else if (lexer.front == '!' || lexer.front == Token.name)
                    {
                        if (lexer.front == '!')
                        {
                            Uneq = -1;
                            lexer.popFront;
                        }
                        else
                        {
                            Uneq = 1;
                        }
                        if (lexer.front == Token.name)
                        {
                            Sym = EAG.FindMNont(lexer.value.to!int);
                            lexer.popFront;
                            if (lexer.front == Token.number)
                            {
                                Num = Uneq * (lexer.value.to!int + 2);
                                lexer.popFront;
                            }
                            else
                            {
                                Num = Uneq;
                            }
                            ++Cnt;
                        }
                        else
                        {
                            Error(lexer.position, "Metanonterminal expected");
                        }
                    }
                    else
                    {
                        Earley.EndAffixform(Pos);
                        break;
                    }
                    Earley.AppMSym(Sym, Num, Pos);
                }
                if (Cnt != 1)
                    Sym = -1;
            }

            EAG.ParamsDesc P;

            P.Params = EAG.empty;
            P.Pos = lexer.position;
            Actual = P;
            Formal = P;
            if (lexer.front == '<')
            {
                lexer.popFront;

                bool isFormal = lexer.front == '+' || lexer.front == '-';

                P.Params = EAG.NextParam;
                while (true)
                {
                    char Dir;
                    int Sym;

                    if (lexer.front == '+' || lexer.front == '-')
                    {
                        if (!isFormal)
                            Error(lexer.position, "'+' or '-' not allowed in actual params");
                        Dir = lexer.front.to!char;
                        lexer.popFront;
                    }
                    else
                    {
                        if (isFormal)
                            Error(lexer.position, "'+' or '-' expected");
                    }
                    EAG.AppParam(Earley.StartAffixform(), lexer.position);
                    Affixform(Sym);
                    if (isFormal)
                    {
                        if (Sym < 0 || lexer.front == ':')
                        {
                            if (lexer.front == ':')
                                lexer.popFront;
                            else
                                Error(lexer.position, "':' expected");
                            if (lexer.front == Token.name)
                            {
                                EAG.AppDom(Dir, EAG.FindMNont(lexer.value.to!int));
                                lexer.popFront;
                            }
                            else
                            {
                                Error(lexer.position, "Metanonterminal expected");
                            }
                            if (lexer.front == Token.number)
                            {
                                Error(lexer.position, "number is not allowed here");
                                lexer.popFront;
                            }
                        }
                        else
                        {
                            EAG.AppDom(Dir, Sym);
                        }
                    }
                    while (lexer.front != ',' && lexer.front != '>' && lexer.front != Token.end)
                    {
                        Error(lexer.position, "symbol not allowed");
                        lexer.popFront;
                    }
                    if (lexer.front == ',')
                        lexer.popFront;
                    else
                        break;
                }
                EAG.AppParam(EAG.nil, lexer.position);
                if (lexer.front == '>')
                    lexer.popFront;
                else
                    Error(lexer.position, "'>' expected");
                if (isFormal)
                    Formal.Params = P.Params;
                else
                    Actual.Params = P.Params;
            }
        }

        /**
         * HyperExpr:
         *   [FormalParams] HyperTerm [ActualParams] {"|" [FormalParams] HyperTerm [ActualParams]}.
         */
        void HyperExpr(int HNont, int Id, char Left, ref EAG.Alt HExpr, Position AltPos)
        {
            /**
             * HyperTerm:
             *   { ident [ActualParams]
             *   | string
             *   | [ActualParams] ( "(" HyperExpr ")"
             *                    | "[" HyperExpr "]" [FormalParams]
             *                    | "{" HyperExpr "}" [FormalParams]  )
             *   } .
             */
            void HyperTerm(ref EAG.ParamsDesc Actual, ref EAG.Factor First, ref EAG.Factor Last)
            {
                int HNont;
                EAG.Alt HExpr;
                EAG.ParamsDesc Formal;
                char Left;
                Position Pos;

                First = null;
                Last = null;
                while (true)
                {
                    if (lexer.front == Token.name)
                    {
                        if (Actual.Params != EAG.empty)
                        {
                            Error(Actual.Pos, "actual params not allowed here");
                            Actual.Params = EAG.empty;
                        }
                        HNont = EAG.FindHNont(lexer.value.to!int);
                        Pos = lexer.position;
                        lexer.popFront;
                        if (lexer.front == Token.number)
                        {
                            Error(lexer.position, "number is not allowed here!");
                            lexer.popFront;
                        }
                        Params(Actual, Formal);
                        if (Formal.Params != EAG.empty)
                            Error(Formal.Pos, "formal params not allowed here");
                        EAG.NewNont(Last, HNont, Actual, Pos);
                        Actual.Params = EAG.empty;
                    }
                    else if (lexer.front == Token.string_)
                    {
                        if (Actual.Params != EAG.empty)
                        {
                            Error(Actual.Pos, "actual params not allowed here");
                            Actual.Params = EAG.empty;
                        }
                        EAG.NewTerm(Last, EAG.FindHTerm(lexer.value.to!int), lexer.position);
                        lexer.popFront;
                    }
                    else
                    {
                        if (Actual.Params == EAG.empty)
                        {
                            Params(Actual, Formal);
                            if (Formal.Params != EAG.empty)
                                Error(Formal.Pos, "formal params not allowed here");
                        }
                        if (lexer.front == '(' || lexer.front == '[' || lexer.front == '{')
                        {
                            Pos = lexer.position;
                            HNont = EAG.NewAnonymNont(Id);
                            EAG.NewNont(Last, HNont, Actual, Pos);
                            Actual.Params = EAG.empty;
                            if (lexer.front == '(')
                            {
                                lexer.popFront;
                                HyperExpr(HNont, Id, '(', HExpr, Pos);
                                if (lexer.front == ')')
                                    lexer.popFront;
                                else
                                    Error(lexer.position, "')' expected");
                                EAG.NewGrp(HNont, HExpr);
                            }
                            else
                            {
                                Left = lexer.front.to!char;
                                lexer.popFront;
                                HyperExpr(HNont, Id, Left, HExpr, Pos);
                                Pos = lexer.position;
                                if (Left == '{')
                                {
                                    if (lexer.front == '}')
                                        lexer.popFront;
                                    else
                                        Error(lexer.position, "'}' expected");
                                }
                                else
                                {
                                    if (lexer.front == ']')
                                        lexer.popFront;
                                    else
                                        Error(lexer.position, "']' expected");
                                }
                                Params(Actual, Formal);
                                if (!EAG.SigOK(HNont))
                                    Error(Formal.Pos, "formal params differ");
                                if (Left == '{')
                                    EAG.NewRep(HNont, HExpr, Formal, Pos);
                                else
                                    EAG.NewOpt(HNont, HExpr, Formal, Pos);
                            }
                        }
                        else
                        {
                            return;
                        }
                    }
                    if (First is null)
                        First = Last;
                }
            }

            EAG.Alt Last = null;

            HExpr = null;
            while (true)
            {
                EAG.ParamsDesc Actual;
                EAG.ParamsDesc Formal;
                EAG.ParamsDesc Formal1;
                EAG.Factor FirstF;
                EAG.Factor LastF;

                Params(Actual, Formal);
                if (!EAG.SigOK(HNont))
                    Error(Formal.Pos, "formal params differ");
                HyperTerm(Actual, FirstF, LastF);
                if (Left == '{' && Actual.Params == EAG.empty)
                {
                    Params(Actual, Formal1);
                    if (Formal1.Params != EAG.empty)
                        Error(Formal1.Pos, "formal params not allowed here");
                }
                else if (Left != '{' && Actual.Params != EAG.empty)
                {
                    Error(Actual.Pos, "actual params not allowed here");
                    Actual.Params = EAG.empty;
                }
                EAG.NewAlt(Last, HNont, Formal, Actual, FirstF, LastF, AltPos);
                if (HExpr is null)
                    HExpr = Last;
                if (lexer.front == '|')
                {
                    AltPos = lexer.position;
                    lexer.popFront;
                }
                else
                {
                    break;
                }
            }
        }

        int HNont = EAG.FindHNont(Id);
        int Sig;
        EAG.Alt HExpr;

        if (!NameNotified && HNont == EAG.firstHNont && ErrorCounter == 0 && lexer.ok)
        {
            NameNotified = true;
            SetBaseName;
            info!"Analysing %s"(EAG.BaseName);
        }
        EAG.HNont[HNont].IsToken = EAG.HNont[HNont].IsToken || IsToken;

        EAG.ParamsDesc Actual;
        EAG.ParamsDesc Formal;

        Params(Actual, Formal);
        if (Actual.Params != EAG.empty)
            Error(Actual.Pos, "actual params not allowed here");
        if (Formal.Params != EAG.empty && EAG.SigOK(HNont))
        {
            Sig = EAG.HNont[HNont].Sig;
            EAG.HNont[HNont].Sig = EAG.empty;
        }

        Position AltPos;

        if (lexer.front == ':')
        {
            AltPos = lexer.position;
            lexer.popFront;
        }
        else
        {
            Error(lexer.position, "':' expected");
        }
        HyperExpr(HNont, Id, '(', HExpr, AltPos);
        if (Formal.Params != EAG.empty)
            Distribute(HNont, HExpr, Sig, Formal);
        EAG.NewGrp(HNont, HExpr);
        if (lexer.front == '.')
            lexer.popFront;
        else
            Error(lexer.position, "'.' expected");
    }

    do
    {
        int Id;
        bool IsToken = false;

        if (lexer.front == Token.name)
        {
            Id = lexer.value.to!int;
            lexer.popFront;
        }
        else
        {
            Error(lexer.position, "identifier of rule expected");
        }
        if (lexer.front == Token.number)
        {
            Error(lexer.position, "number is not allowed here");
            lexer.popFront;
        }
        if (lexer.front == '*')
        {
            IsToken = true;
            lexer.popFront;
        }
        if (lexer.front == '=')
            MetaRule(Id, IsToken);
        else
            HyperRule(Id, IsToken);
        if (lexer.front != Token.name && lexer.front != Token.end)
        {
            Error(lexer.position, "not allowed symbol");
            do
                lexer.popFront;
            while (lexer.front != '.' && lexer.front != Token.end);
            if (lexer.front != Token.end)
                lexer.popFront;
            Error(lexer.position, "    restart point");
        }
    }
    while (lexer.front != Token.end);
    ErrorCounter += lexer.ok ? 0 : 1;
}

void CheckSemantics()
{
    void Shrink(int Sym)
    {
        if (EAG.HNont[Sym].Id >= 0 && cast(EAG.Grp) EAG.HNont[Sym].Def)
        {
            EAG.Alt A = (cast(EAG.Grp) EAG.HNont[Sym].Def).Sub;

            if (A.Formal.Params == EAG.empty && A.Next is null && A.Sub !is null && cast(EAG.Nont) A.Sub)
            {
                EAG.Nont F = cast(EAG.Nont) A.Sub;

                if (EAG.HNont[F.Sym].anonymous && F.Actual.Params == EAG.empty && F.Next is null)
                {
                    EAG.HNont[Sym].Def = EAG.HNont[F.Sym].Def;
                    EAG.HNont[F.Sym].Def = null;
                    EAG.HNont[Sym].Sig = EAG.HNont[F.Sym].Sig;
                    A = EAG.HNont[Sym].Def.Sub;
                    do
                    {
                        A.Up = Sym;
                        A = A.Next;
                    }
                    while (A !is null);
                }
            }
        }
    }

    void Traverse(int Sym)
    {
        void CheckParamList(int Dom, EAG.ParamsDesc Par, bool Lhs)
        {
            import std.math : abs;

            int P = Par.Params;

            while (EAG.DomBuf[Dom] != nil && EAG.ParamBuf[P].Affixform != nil)
            {
                EAG.ParamBuf[P].isDef = Lhs && EAG.DomBuf[Dom] < 0 || !Lhs && EAG.DomBuf[Dom] > 0;
                Earley.Parse(abs(EAG.DomBuf[Dom]), EAG.ParamBuf[P].Affixform,
                        EAG.ParamBuf[P].Affixform, EAG.ParamBuf[P].isDef);
                if (EAG.ParamBuf[P].Affixform == EAG.nil)
                    ++ErrorCounter;
                ++Dom;
                ++P;
            }
            if (EAG.DomBuf[Dom] != EAG.ParamBuf[P].Affixform)
            {
                Error(Par.Pos, "number of affixforms differs from signature");
            }
        }

        void CheckActual(EAG.Nont F)
        {
            if (EAG.WellMatched(EAG.HNont[F.Sym].Sig, EAG.empty)
                    && F.Actual.Params != EAG.empty
                    && F.Next !is null
                    && cast(EAG.Nont) F.Next
                    && (cast(EAG.Nont) F.Next).Actual.Params == EAG.empty
                    && EAG.HNont[(cast(EAG.Nont) F.Next).Sym].anonymous)
            {
                (cast(EAG.Nont)F.Next).Actual = F.Actual;
                F.Actual.Params = EAG.empty;
            }
        }

        void CheckRep(EAG.Alt A)
        {
            if (A.Last !is null)
                if (auto F = cast(EAG.Nont) A.Last)
                {
                    if (EAG.WellMatched(EAG.HNont[F.Sym].Sig, EAG.empty)
                            && F.Actual.Params != EAG.empty
                            && A.Actual.Params == EAG.empty)
                    {
                        A.Actual = F.Actual;
                        F.Actual.Params = EAG.empty;
                    }
                }
        }

        EAG.Rule Node = EAG.HNont[Sym].Def;
        const Sig = EAG.HNont[Sym].Sig;

        if (Node !is null)
        {
            if (auto rep = cast(EAG.Rep) Node)
            {
                EAG.Scope = EAG.NextVar;
                rep.Scope.Beg = EAG.NextVar;
                CheckParamList(Sig, rep.Formal, true);
                rep.Scope.End = EAG.NextVar;
            }
            else if (auto opt = cast(EAG.Opt) Node)
            {
                EAG.Scope = EAG.NextVar;
                opt.Scope.Beg = EAG.NextVar;
                CheckParamList(Sig, opt.Formal, true);
                opt.Scope.End = EAG.NextVar;
            }

            EAG.Alt A = Node.Sub;

            do
            {
                EAG.Scope = EAG.NextVar;
                A.Scope.Beg = EAG.NextVar;
                CheckParamList(Sig, A.Formal, true);
                if (cast(EAG.Rep) Node)
                {
                    CheckRep(A);
                    CheckParamList(Sig, A.Actual, false);
                }

                EAG.Factor F = A.Sub;

                while (F !is null)
                {
                    if (auto nont = cast(EAG.Nont) F)
                    {
                        CheckActual(nont);
                        CheckParamList(EAG.HNont[nont.Sym].Sig, nont.Actual, false);
                    }
                    F = F.Next;
                }
                A.Scope.End = EAG.NextVar;
                A = A.Next;
            }
            while (A !is null);
        }
    }

    EAG.All = BitArray();
    EAG.All.length = EAG.NextHNont + 1;
    if (EAG.firstHNont == EAG.NextHNont)
    {
        ++ErrorCounter;
        error!"EAG needs at least one hyper-rule";
    }
    for (int Sym = EAG.firstHNont; Sym < EAG.NextHNont; ++Sym)
    {
        if (EAG.HNont[Sym].Def is null)
        {
            if (EAG.HNont[Sym].Id >= 0)
            {
                ++ErrorCounter;
                error!"hyper-nonterminal %s undefined"(EAG.symbolTable.symbol(EAG.HNont[Sym].Id));
            }
        }
        else
        {
            EAG.All[Sym] = true;
            Shrink(Sym);
        }
    }
    for (int Sym = EAG.firstMNont; Sym < EAG.NextMNont; ++Sym)
    {
        if (EAG.MNont[Sym].MRule == nil)
        {
            ++ErrorCounter;
            error!"meta-nonterminal %s undefined"(EAG.symbolTable.symbol(EAG.MNont[Sym].Id));
        }
    }
    if (ErrorCounter == 0)
    {
        for (int Sym = EAG.firstHNont; Sym < EAG.NextHNont; ++Sym)
            Traverse(Sym);
        for (int n = EAG.firstVar; n < EAG.NextVar; ++n)
        {
            if (EAG.Var[n].Num < 0 && EAG.Var[n].Neg == EAG.nil)
                Error(EAG.Var[n].Pos, "! operator not allowed");
            if (!EAG.Var[n].Def)
            {
                import std.format : format;

                Error(EAG.Var[n].Pos, format!"variable %s never on defining position"(EAG.VarRepr(n)));
            }
        }
        if (EAG.DomBuf[EAG.HNont[EAG.StartSym].Sig] == EAG.nil
                || EAG.DomBuf[EAG.HNont[EAG.StartSym].Sig] < 0
                || EAG.DomBuf[EAG.HNont[EAG.StartSym].Sig + 1] != EAG.nil)
        {
            ++ErrorCounter;
            error!"start symbol %s must have exactly one synthesized attribute"(
                    EAG.symbolTable.symbol(EAG.HNont[EAG.StartSym].Id));
        }
        if (EAG.firstMNont == EAG.NextMNont)
        {
            ++ErrorCounter;
            error!"EAG needs at least one meta-rule";
        }
    }
}

void ComputeEAGSets()
{
    struct EdgeRecord
    {
        EAG.Alt Dest;
        int Next;
    }

    EdgeRecord[] Edge;
    int NextEdge;
    int[] Deg;
    int[] Stack;
    int Top;
    BitArray Prod;

    void ComputeReach(int Sym)
    {
        EAG.Alt A = EAG.HNont[Sym].Def.Sub;

        EAG.Reach[Sym] = true;
        do
        {
            for (EAG.Factor F = A.Sub; F !is null; F = F.Next)
                if (auto nont = cast(EAG.Nont) F)
                    if (!EAG.Reach[nont.Sym])
                        ComputeReach(nont.Sym);
            A = A.Next;
        }
        while (A !is null);
    }

    void NewEdge(int From, EAG.Alt To)
    {
        Edge[NextEdge].Dest = To;
        Edge[NextEdge].Next = Edge[From].Next;
        Edge[From].Next = NextEdge;
        ++NextEdge;
    }

    void TestDeg(EAG.Alt A)
    {
        if (Deg[A.Ind] == 0)
        {
            if (!Prod[A.Up])
            {
                Prod[A.Up] = true;
                Stack[Top] = A.Up;
                ++Top;
            }
        }
    }

    void Prune()
    {
        int E;
        EAG.Alt A;
        while (Top > 0)
        {
            --Top;
            E = Edge[Stack[Top]].Next;
            while (E != nil)
            {
                A = Edge[E].Dest;
                --Deg[A.Ind];
                TestDeg(A);
                E = Edge[E].Next;
            }
        }
    }

    long Warnings = 0;

    EAG.Reach = BitArray();
    EAG.Reach.length = EAG.NextHNont + 1;

    ComputeReach(EAG.StartSym);
    for (int Sym = EAG.firstHNont; Sym < EAG.NextHNont; ++Sym)
        if (EAG.HNont[Sym].Def !is null && !EAG.Reach[Sym] && EAG.HNont[Sym].Id >= 0)
            ++Warnings;
    Deg = new int[EAG.NextHAlt];
    Stack = new int[EAG.NextHNont];
    Top = 0;
    Edge = new EdgeRecord[EAG.NextHNont + EAG.NONont + 1];
    NextEdge = EAG.NextHNont;
    for (int Sym = EAG.firstHNont; Sym < EAG.NextHNont; ++Sym)
        Edge[Sym].Next = nil;
    EAG.Null = BitArray();
    EAG.Null.length = EAG.NextHNont + 1;
    Prod = BitArray();
    Prod.length = EAG.NextHNont + 1;
    for (int Sym = EAG.firstHNont; Sym < EAG.NextHNont; ++Sym)
    {
        if (EAG.HNont[Sym].Def !is null)
        {
            if (cast(EAG.Opt) EAG.HNont[Sym].Def || cast(EAG.Rep) EAG.HNont[Sym].Def)
            {
                Prod[Sym] = true;
                Stack[Top] = Sym;
                ++Top;
            }

            EAG.Alt A = EAG.HNont[Sym].Def.Sub;

            do
            {
                bool TermFound = false;

                Deg[A.Ind] = 0;
                for (EAG.Factor F = A.Sub; F !is null; F = F.Next)
                {
                    if (cast(EAG.Term) F)
                    {
                        TermFound = true;
                    }
                    else if (auto nont = cast(EAG.Nont) F)
                    {
                        ++Deg[A.Ind];
                        NewEdge(nont.Sym, A);
                    }
                }
                if (TermFound)
                    Deg[A.Ind] += int.min;
                else
                    TestDeg(A);
                A = A.Next;
            }
            while (A !is null);
        }
    }
    Prune;
    EAG.Null = Prod.dup;
    for (int Sym = EAG.firstHNont; Sym < EAG.NextHNont; ++Sym)
    {
        if (EAG.HNont[Sym].Def !is null)
        {
            EAG.Alt A = EAG.HNont[Sym].Def.Sub;

            do
            {
                if (Deg[A.Ind] < 0)
                {
                    Deg[A.Ind] -= int.min;
                    TestDeg(A);
                }
                A = A.Next;
            }
            while (A !is null);
        }
    }
    Prune;
    EAG.Prod = Prod;
    Warnings += (EAG.All & ~EAG.Prod).count;
    if (Warnings > 0)
        warn!"%s warnings"(Warnings);
}

void Analyse(Input input)
{
    EAG.Init;
    lexer = Lexer(input, EAG.symbolTable);
    Earley.Init;
    ErrorCounter = 0;
    NameNotified = false;
    Specification;
    if (ErrorCounter == 0)
    {
        CheckSemantics;
        Earley.Finit;
    }
    if (ErrorCounter == 0)
    {
        ComputeEAGSets;
    }
    if (ErrorCounter == 0)
    {
        EAG.History |= EAG.analysed;
        info!"%s grammar is valid"(EAG.BaseName);
    }
    else
    {
        EAG.History &= ~EAG.analysed;
        if (NameNotified)
            error!"errors in %s"(EAG.BaseName);
        else
            error!"errors";
    }
}

void Warnings()
in (EAG.Performed(EAG.analysed))
{
    const Unreach = EAG.All - EAG.Reach;
    const Unprod = EAG.All - EAG.Prod;
    const NoWarnings = Unreach.bitsSet.empty && Unprod.bitsSet.empty;

    if (NoWarnings)
    {
        info!"Analyser: no warnings on %s's hyper-nonterminals"(EAG.BaseName);
        return;
    }
    warn!"Analyser warnings on %s's hyper-nonterminals:"(EAG.BaseName);
    for (int Sym = EAG.firstHNont; Sym < EAG.NextHNont; ++Sym)
    {
        if (Unreach[Sym] && EAG.HNont[Sym].Id >= 0)
            warn!"%s unreachable"(EAG.HNontRepr(Sym));
        if (Unprod[Sym])
        {
            if (EAG.HNont[Sym].anonymous)
                warn!"anonymous nonterminal in %s unproductive"(EAG.NamedHNontRepr(Sym));
            else
                warn!"%s unproductive"(EAG.HNontRepr(Sym));
        }
    }
}

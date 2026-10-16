module epsilon.analyzer;

import epsilon.eag;
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
 *   {WhiteSpaceRule | MetaRule | HyperRule}.
 */
void Specification()
{
    /**
     * WhiteSpaceRule:
     *   ':' WhiteSpaceDefinition {'|' WhiteSpaceDefinition} '.'.
     */
    void WhiteSpaceRule()
    in (lexer.front == ':')
    {
        /**
         * WhiteSpaceDefinition:
         *     string                  ! white space
         *   | string '~'              ! comment that extends to end of line
         *   | string '~' string       ! comment in brackets
         *   | string '~' '~' string.  ! nesting comment in brackets
         */
        void WhiteSpaceDefinition()
        in (lexer.front == Token.string_)
        {
            lexer.popFront;

            if (lexer.front == '~')
            {
                bool nestingComment = false;

                lexer.popFront;
                if (lexer.front == '~')
                {
                    nestingComment = true;
                    lexer.popFront;
                }
                if (lexer.front == Token.string_)
                    lexer.popFront;
                else if (nestingComment)
                    Error(lexer.position, "closing bracket for nesting comment expected");
            }
        }

        warn!"skipping not yet supported whitespace rule\n%s"(lexer.position);
        lexer.popFront;

        for (;;)
        {
            if (lexer.front == Token.string_)
                WhiteSpaceDefinition;
            else
                Error(lexer.position, "white space definition expected");
            if (!lexer.empty && lexer.front != '|' && lexer.front != '.')
            {  // sync
                Error(lexer.position, "unexpected symbol");
                do
                    lexer.popFront;
                while (!lexer.empty && lexer.front != '|' && lexer.front != '.');
            }
            if (lexer.front == '|')
                lexer.popFront;
            else
                break;
        }

        assert(lexer.empty || lexer.front == '.');

        if (lexer.front == '.')
            lexer.popFront;
        else
            Error(lexer.position, `symbol "." expected`);
    }

    /**
     * MetaRule:
     *   ident "=" MetaExpr ".".
     */
    void MetaRule(int Id, bool IsToken)
    {
        const MNont = eag.FindMNont(Id);

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
                for (;;)
                {
                    if (lexer.front == Token.name)
                    {
                        eag.AppMemb(eag.FindMNont(lexer.value.to!int));
                        lexer.popFront;
                        if (lexer.front == Token.number)
                        {
                            Error(lexer.position, "number is not allowed here");
                            lexer.popFront;
                        }
                    }
                    else if (lexer.front == Token.string_)
                    {
                        eag.AppMemb(-eag.FindMTerm(lexer.value.to!int));
                        lexer.popFront;
                    }
                    else
                    {
                        eag.AppMemb(EAG.nil);
                        break;
                    }
                }
            }

            for (;;)
            {
                const Rhs = eag.NextMemb;

                MetaTerm;
                eag.AppMemb(eag.NewMAlt(MNont, Rhs));
                if (lexer.front == '|')
                    lexer.popFront;
                else
                    break;
            }
        }

        eag.MNont[MNont].IsToken = eag.MNont[MNont].IsToken || IsToken;
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
        eag.StartSym = EAG.firstHNont;
        eag.BaseName = eag.symbolTable.symbol(eag.HNont[eag.StartSym].Id);
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

                d = eag.NextParam;
                while (eag.ParamBuf[P].Affixform != nil)
                {
                    Earley.CopyAffixform(eag.ParamBuf[P].Affixform, Affixform);
                    eag.AppParam(Affixform, eag.ParamBuf[P].Pos);
                    ++P;
                }
                eag.AppParam(nil, eag.ParamBuf[P].Pos);
            }

            eag.HNont[Sym].Sig = Sig;
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

                for (;;)
                {
                    short Uneq;
                    int Num;
                    Position Pos = lexer.position;

                    if (lexer.front == Token.string_)
                    {
                        Sym = -eag.FindMTerm(lexer.value.to!int);
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
                            Sym = eag.FindMNont(lexer.value.to!int);
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

                P.Params = eag.NextParam;
                for (;;)
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
                    eag.AppParam(Earley.StartAffixform(), lexer.position);
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
                                eag.AppDom(Dir, eag.FindMNont(lexer.value.to!int));
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
                            eag.AppDom(Dir, Sym);
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
                eag.AppParam(EAG.nil, lexer.position);
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
                for (;;)
                {
                    if (lexer.front == Token.name)
                    {
                        if (Actual.Params != EAG.empty)
                        {
                            Error(Actual.Pos, "actual params not allowed here");
                            Actual.Params = EAG.empty;
                        }
                        HNont = eag.FindHNont(lexer.value.to!int);
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
                        eag.NewNont(Last, HNont, Actual, Pos);
                        Actual.Params = EAG.empty;
                    }
                    else if (lexer.front == Token.string_)
                    {
                        if (Actual.Params != EAG.empty)
                        {
                            Error(Actual.Pos, "actual params not allowed here");
                            Actual.Params = EAG.empty;
                        }
                        eag.NewTerm(Last, eag.FindHTerm(lexer.value.to!int), lexer.position);
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
                            HNont = eag.NewAnonymNont(Id);
                            eag.NewNont(Last, HNont, Actual, Pos);
                            Actual.Params = EAG.empty;
                            if (lexer.front == '(')
                            {
                                lexer.popFront;
                                HyperExpr(HNont, Id, '(', HExpr, Pos);
                                if (lexer.front == ')')
                                    lexer.popFront;
                                else
                                    Error(lexer.position, "')' expected");
                                eag.NewGrp(HNont, HExpr);
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
                                if (!eag.SigOK(HNont))
                                    Error(Formal.Pos, "formal params differ");
                                if (Left == '{')
                                    eag.NewRep(HNont, HExpr, Formal, Pos);
                                else
                                    eag.NewOpt(HNont, HExpr, Formal, Pos);
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
            for (;;)
            {
                EAG.ParamsDesc Actual;
                EAG.ParamsDesc Formal;
                EAG.ParamsDesc Formal1;
                EAG.Factor FirstF;
                EAG.Factor LastF;

                Params(Actual, Formal);
                if (!eag.SigOK(HNont))
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
                eag.NewAlt(Last, HNont, Formal, Actual, FirstF, LastF, AltPos);
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

        int HNont = eag.FindHNont(Id);
        int Sig;
        EAG.Alt HExpr;

        if (!NameNotified && HNont == EAG.firstHNont && ErrorCounter == 0 && lexer.ok)
        {
            NameNotified = true;
            SetBaseName;
            info!"Analysing %s"(eag.BaseName);
        }
        eag.HNont[HNont].IsToken = eag.HNont[HNont].IsToken || IsToken;

        EAG.ParamsDesc Actual;
        EAG.ParamsDesc Formal;

        Params(Actual, Formal);
        if (Actual.Params != EAG.empty)
            Error(Actual.Pos, "actual params not allowed here");
        if (Formal.Params != EAG.empty && eag.SigOK(HNont))
        {
            Sig = eag.HNont[HNont].Sig;
            eag.HNont[HNont].Sig = EAG.empty;
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
        eag.NewGrp(HNont, HExpr);
        if (lexer.front == '.')
            lexer.popFront;
        else
            Error(lexer.position, "'.' expected");
    }

    do
    {
        int Id;
        bool IsToken = false;

        if (lexer.front == ':')
        {
            WhiteSpaceRule;
            continue;
        }
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
        if (lexer.front != ':' && lexer.front != Token.name && lexer.front != Token.end)
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
        if (eag.HNont[Sym].Id >= 0 && cast(EAG.Grp) eag.HNont[Sym].Def)
        {
            EAG.Alt A = (cast(EAG.Grp) eag.HNont[Sym].Def).Sub;

            if (A.Formal.Params == EAG.empty && A.Next is null && A.Sub !is null && cast(EAG.Nont) A.Sub)
            {
                EAG.Nont F = cast(EAG.Nont) A.Sub;

                if (eag.HNont[F.Sym].anonymous && F.Actual.Params == EAG.empty && F.Next is null)
                {
                    eag.HNont[Sym].Def = eag.HNont[F.Sym].Def;
                    eag.HNont[F.Sym].Def = null;
                    eag.HNont[Sym].Sig = eag.HNont[F.Sym].Sig;
                    A = eag.HNont[Sym].Def.Sub;
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

            while (eag.DomBuf[Dom] != nil && eag.ParamBuf[P].Affixform != nil)
            {
                eag.ParamBuf[P].isDef = Lhs && eag.DomBuf[Dom] < 0 || !Lhs && eag.DomBuf[Dom] > 0;
                Earley.Parse(abs(eag.DomBuf[Dom]), eag.ParamBuf[P].Affixform,
                        eag.ParamBuf[P].Affixform, eag.ParamBuf[P].isDef);
                if (eag.ParamBuf[P].Affixform == EAG.nil)
                    ++ErrorCounter;
                ++Dom;
                ++P;
            }
            if (eag.DomBuf[Dom] != eag.ParamBuf[P].Affixform)
            {
                Error(Par.Pos, "number of affixforms differs from signature");
            }
        }

        void CheckActual(EAG.Nont F)
        {
            if (eag.WellMatched(eag.HNont[F.Sym].Sig, EAG.empty)
                    && F.Actual.Params != EAG.empty
                    && F.Next !is null
                    && cast(EAG.Nont) F.Next
                    && (cast(EAG.Nont) F.Next).Actual.Params == EAG.empty
                    && eag.HNont[(cast(EAG.Nont) F.Next).Sym].anonymous)
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
                    if (eag.WellMatched(eag.HNont[F.Sym].Sig, EAG.empty)
                            && F.Actual.Params != EAG.empty
                            && A.Actual.Params == EAG.empty)
                    {
                        A.Actual = F.Actual;
                        F.Actual.Params = EAG.empty;
                    }
                }
        }

        EAG.Rule Node = eag.HNont[Sym].Def;
        const Sig = eag.HNont[Sym].Sig;

        if (Node !is null)
        {
            if (auto rep = cast(EAG.Rep) Node)
            {
                eag.Scope = eag.NextVar;
                rep.Scope.Beg = eag.NextVar;
                CheckParamList(Sig, rep.Formal, true);
                rep.Scope.End = eag.NextVar;
            }
            else if (auto opt = cast(EAG.Opt) Node)
            {
                eag.Scope = eag.NextVar;
                opt.Scope.Beg = eag.NextVar;
                CheckParamList(Sig, opt.Formal, true);
                opt.Scope.End = eag.NextVar;
            }

            EAG.Alt A = Node.Sub;

            do
            {
                eag.Scope = eag.NextVar;
                A.Scope.Beg = eag.NextVar;
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
                        CheckParamList(eag.HNont[nont.Sym].Sig, nont.Actual, false);
                    }
                    F = F.Next;
                }
                A.Scope.End = eag.NextVar;
                A = A.Next;
            }
            while (A !is null);
        }
    }

    eag.All = BitArray();
    eag.All.length = eag.NextHNont + 1;
    if (EAG.firstHNont == eag.NextHNont)
    {
        ++ErrorCounter;
        error!"EAG needs at least one hyper-rule";
    }
    for (int Sym = EAG.firstHNont; Sym < eag.NextHNont; ++Sym)
    {
        if (eag.HNont[Sym].Def is null)
        {
            if (eag.HNont[Sym].Id >= 0)
            {
                ++ErrorCounter;
                error!"hyper-nonterminal %s undefined"(eag.symbolTable.symbol(eag.HNont[Sym].Id));
            }
        }
        else
        {
            eag.All[Sym] = true;
            Shrink(Sym);
        }
    }
    for (int Sym = EAG.firstMNont; Sym < eag.NextMNont; ++Sym)
    {
        if (eag.MNont[Sym].MRule == nil)
        {
            ++ErrorCounter;
            error!"meta-nonterminal %s undefined"(eag.symbolTable.symbol(eag.MNont[Sym].Id));
        }
    }
    if (ErrorCounter == 0)
    {
        for (int Sym = EAG.firstHNont; Sym < eag.NextHNont; ++Sym)
            Traverse(Sym);
        for (int n = EAG.firstVar; n < eag.NextVar; ++n)
        {
            if (eag.Var[n].Num < 0 && eag.Var[n].Neg == EAG.nil)
                Error(eag.Var[n].Pos, "! operator not allowed");
            if (!eag.Var[n].Def)
            {
                import std.format : format;

                Error(eag.Var[n].Pos, format!"variable %s never on defining position"(eag.VarRepr(n)));
            }
        }
        if (eag.DomBuf[eag.HNont[eag.StartSym].Sig] == EAG.nil
                || eag.DomBuf[eag.HNont[eag.StartSym].Sig] < 0
                || eag.DomBuf[eag.HNont[eag.StartSym].Sig + 1] != EAG.nil)
        {
            ++ErrorCounter;
            error!"start symbol %s must have exactly one synthesized attribute"(
                    eag.symbolTable.symbol(eag.HNont[eag.StartSym].Id));
        }
        if (EAG.firstMNont == eag.NextMNont)
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
        EAG.Alt A = eag.HNont[Sym].Def.Sub;

        eag.Reach[Sym] = true;
        do
        {
            for (EAG.Factor F = A.Sub; F !is null; F = F.Next)
                if (auto nont = cast(EAG.Nont) F)
                    if (!eag.Reach[nont.Sym])
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

    eag.Reach = BitArray();
    eag.Reach.length = eag.NextHNont + 1;

    ComputeReach(eag.StartSym);
    Deg = new int[eag.NextHAlt];
    Stack = new int[eag.NextHNont];
    Top = 0;
    Edge = new EdgeRecord[eag.NextHNont + eag.NONont + 1];
    NextEdge = eag.NextHNont;
    for (int Sym = EAG.firstHNont; Sym < eag.NextHNont; ++Sym)
        Edge[Sym].Next = nil;
    eag.Null = BitArray();
    eag.Null.length = eag.NextHNont + 1;
    Prod = BitArray();
    Prod.length = eag.NextHNont + 1;
    for (int Sym = EAG.firstHNont; Sym < eag.NextHNont; ++Sym)
    {
        if (eag.HNont[Sym].Def !is null)
        {
            if (cast(EAG.Opt) eag.HNont[Sym].Def || cast(EAG.Rep) eag.HNont[Sym].Def)
            {
                Prod[Sym] = true;
                Stack[Top] = Sym;
                ++Top;
            }

            EAG.Alt A = eag.HNont[Sym].Def.Sub;

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
    eag.Null = Prod.dup;
    for (int Sym = EAG.firstHNont; Sym < eag.NextHNont; ++Sym)
    {
        if (eag.HNont[Sym].Def !is null)
        {
            EAG.Alt A = eag.HNont[Sym].Def.Sub;

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
    eag.Prod = Prod;
}

void Analyse(Input input)
{
    eag.Init;
    lexer = Lexer(input, eag.symbolTable);
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
        if (!eag.Prod[eag.StartSym])
        {
            ++ErrorCounter;
            error!"start symbol %s is unproductive"(eag.HNontRepr(eag.StartSym));
        }
    }
    if (ErrorCounter == 0)
    {
        info!"%s grammar is valid"(eag.BaseName);
    }
    else
    {
        if (NameNotified)
            info!"errors in %s"(eag.BaseName);
        else
            info!"errors";
    }
}

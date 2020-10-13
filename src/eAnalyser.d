module eAnalyser;

import EAG = eEAG;
import Earley = eEarley;
import Scanner = eScanner;
import io : Position, TextIn;
import log;
import runtime;
import std.bitmanip : BitArray;

const nil = EAG.nil;
char Tok;
int ErrorCounter;
bool NameNotified;

void Error(Position Pos, string ErrMsg)
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
    int Id;
    bool IsToken;
    /**
     * MetaRule:
     *   ident "=" MetaExpr ".".
     */
    void MetaRule(int Id, bool IsToken)
    {
        int MNont;
        /**
         * MetaExpr:
         *   MetaTerm {"|" MetaTerm}.
         */
        void MetaExpr()
        {
            int Rhs;
            /**
             * MetaTerm:
             *   {ident | string}.
             */
            void MetaTerm()
            {
                while (true)
                {
                    if (Tok == Scanner.ide)
                    {
                        EAG.AppMemb(EAG.FindMNont(Scanner.Val));
                        Scanner.Get(Tok);
                        if (Tok == Scanner.num)
                        {
                            Error(Scanner.Pos, "number is not allowed here");
                            Scanner.Get(Tok);
                        }
                    }
                    else if (Tok == Scanner.str)
                    {
                        EAG.AppMemb(-EAG.FindMTerm(Scanner.Val));
                        Scanner.Get(Tok);
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
                Rhs = EAG.NextMemb;
                MetaTerm;
                EAG.AppMemb(EAG.NewMAlt(MNont, Rhs));
                if (Tok == '|')
                {
                    Scanner.Get(Tok);
                }
                else
                {
                    break;
                }
            }
        }

        MNont = EAG.FindMNont(Id);
        EAG.MNont[MNont].IsToken = EAG.MNont[MNont].IsToken || IsToken;
        if (Tok == '=')
        {
            Scanner.Get(Tok);
        }
        else
        {
            Error(Scanner.Pos, "'=' expected");
        }
        MetaExpr;
        if (Tok == '.')
        {
            Scanner.Get(Tok);
        }
        else
        {
            Error(Scanner.Pos, "'.' expected");
        }
    }

    void SetBaseName()
    {
        EAG.StartSym = EAG.firstHNont;
        EAG.BaseName = Scanner.repr(EAG.HNont[EAG.StartSym].Id);
    }

    /**
     * HyperRule:
     *   ident [FormalParams] ":" HyperExpr ".".
     */
    void HyperRule(int Id, bool IsToken)
    {
        int HNont;
        int Sig;
        EAG.Alt HExpr;
        EAG.ParamsDesc Actual;
        EAG.ParamsDesc Formal;
        Position AltPos;

        void Distribute(int Sym, EAG.Alt A, int Sig, EAG.ParamsDesc Formal)
        {
            void CopyParams(ref int s, ref int d)
            {
                int Affixform;
                int P;
                d = EAG.NextParam;
                P = s;
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
            EAG.ParamsDesc P;
            bool isFormal;
            char Dir;
            int Sym;

            /**
             * Affixform:
             *   {string | ["#"] ident [number]}.
             */
            void Affixform(ref int Sym)
            {
                short Uneq;
                int Cnt;
                int Num;
                Position Pos;
                Cnt = 0;
                while (true)
                {
                    Pos = Scanner.Pos;
                    if (Tok == Scanner.str)
                    {
                        Sym = -EAG.FindMTerm(Scanner.Val);
                        Num = 0;
                        Scanner.Get(Tok);
                        ++Cnt;
                    }
                    else if (Tok == '#' || Tok == Scanner.ide)
                    {
                        if (Tok == '#')
                        {
                            Uneq = -1;
                            Scanner.Get(Tok);
                        }
                        else
                        {
                            Uneq = 1;
                        }
                        if (Tok == Scanner.ide)
                        {
                            Sym = EAG.FindMNont(Scanner.Val);
                            Scanner.Get(Tok);
                            if (Tok == Scanner.num)
                            {
                                Num = Uneq * (Scanner.Val + 2);
                                Scanner.Get(Tok);
                            }
                            else
                            {
                                Num = Uneq;
                            }
                            ++Cnt;
                        }
                        else
                        {
                            Error(Scanner.Pos, "Metanonterminal expected");
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
                {
                    Sym = -1;
                }
            }

            P.Params = EAG.empty;
            P.Pos = Scanner.Pos;
            Actual = P;
            Formal = P;
            if (Tok == '<')
            {
                Scanner.Get(Tok);
                isFormal = Tok == '+' || Tok == '-';
                P.Params = EAG.NextParam;
                while (true)
                {
                    if (Tok == '+' || Tok == '-')
                    {
                        if (!isFormal)
                        {
                            Error(Scanner.Pos, "'+' or '-' not allowed in actual params");
                        }
                        Dir = Tok;
                        Scanner.Get(Tok);
                    }
                    else
                    {
                        if (isFormal)
                        {
                            Error(Scanner.Pos, "'+' or '-' expected");
                        }
                    }
                    EAG.AppParam(Earley.StartAffixform(), Scanner.Pos);
                    Affixform(Sym);
                    if (isFormal)
                    {
                        if (Sym < 0 || Tok == ':')
                        {
                            if (Tok == ':')
                            {
                                Scanner.Get(Tok);
                            }
                            else
                            {
                                Error(Scanner.Pos, "':' expected");
                            }
                            if (Tok == Scanner.ide)
                            {
                                EAG.AppDom(Dir, EAG.FindMNont(Scanner.Val));
                                Scanner.Get(Tok);
                            }
                            else
                            {
                                Error(Scanner.Pos, "Metanonterminal expected");
                            }
                            if (Tok == Scanner.num)
                            {
                                Error(Scanner.Pos, "number is not allowed here");
                                Scanner.Get(Tok);
                            }
                        }
                        else
                        {
                            EAG.AppDom(Dir, Sym);
                        }
                    }
                    while (Tok != ',' && Tok != '>' && Tok != Scanner.eot)
                    {
                        Error(Scanner.Pos, "symbol not allowed");
                        Scanner.Get(Tok);
                    }
                    if (Tok == ',')
                    {
                        Scanner.Get(Tok);
                    }
                    else
                    {
                        break;
                    }
                }
                EAG.AppParam(EAG.nil, Scanner.Pos);
                if (Tok == '>')
                {
                    Scanner.Get(Tok);
                }
                else
                {
                    Error(Scanner.Pos, "'>' expected");
                }
                if (isFormal)
                {
                    Formal.Params = P.Params;
                }
                else
                {
                    Actual.Params = P.Params;
                }
            }
        }
        /**
         * HyperExpr:
         *   [FormalParams] HyperTerm [ActualParams] {"|" [FormalParams] HyperTerm [ActualParams]}.
         */
        void HyperExpr(int HNont, int Id, char Left, ref EAG.Alt HExpr, Position AltPos)
        {
            EAG.ParamsDesc Actual;
            EAG.ParamsDesc Formal;
            EAG.ParamsDesc Formal1;
            EAG.Alt Last;
            EAG.Factor FirstF;
            EAG.Factor LastF;
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
                    if (Tok == Scanner.ide)
                    {
                        if (Actual.Params != EAG.empty)
                        {
                            Error(Actual.Pos, "actual params not allowed here");
                            Actual.Params = EAG.empty;
                        }
                        HNont = EAG.FindHNont(Scanner.Val);
                        Pos = Scanner.Pos;
                        Scanner.Get(Tok);
                        if (Tok == Scanner.num)
                        {
                            Error(Scanner.Pos, "number is not allowed here!");
                            Scanner.Get(Tok);
                        }
                        Params(Actual, Formal);
                        if (Formal.Params != EAG.empty)
                        {
                            Error(Formal.Pos, "formal params not allowed here");
                        }
                        EAG.NewNont(Last, HNont, Actual, Pos);
                        Actual.Params = EAG.empty;
                    }
                    else if (Tok == Scanner.str)
                    {
                        if (Actual.Params != EAG.empty)
                        {
                            Error(Actual.Pos, "actual params not allowed here");
                            Actual.Params = EAG.empty;
                        }
                        EAG.NewTerm(Last, EAG.FindHTerm(Scanner.Val), Scanner.Pos);
                        Scanner.Get(Tok);
                    }
                    else
                    {
                        if (Actual.Params == EAG.empty)
                        {
                            Params(Actual, Formal);
                            if (Formal.Params != EAG.empty)
                            {
                                Error(Formal.Pos, "formal params not allowed here");
                            }
                        }
                        if (Tok == '(' || Tok == '[' || Tok == '{')
                        {
                            Pos = Scanner.Pos;
                            HNont = EAG.NewAnonymNont(Id);
                            EAG.NewNont(Last, HNont, Actual, Pos);
                            Actual.Params = EAG.empty;
                            if (Tok == '(')
                            {
                                Scanner.Get(Tok);
                                HyperExpr(HNont, Id, '(', HExpr, Pos);
                                if (Tok == ')')
                                {
                                    Scanner.Get(Tok);
                                }
                                else
                                {
                                    Error(Scanner.Pos, "')' expected");
                                }
                                EAG.NewGrp(HNont, HExpr);
                            }
                            else
                            {
                                Left = Tok;
                                Scanner.Get(Tok);
                                HyperExpr(HNont, Id, Left, HExpr, Pos);
                                Pos = Scanner.Pos;
                                if (Left == '{')
                                {
                                    if (Tok == '}')
                                    {
                                        Scanner.Get(Tok);
                                    }
                                    else
                                    {
                                        Error(Scanner.Pos, "'}' expected");
                                    }
                                }
                                else
                                {
                                    if (Tok == ']')
                                    {
                                        Scanner.Get(Tok);
                                    }
                                    else
                                    {
                                        Error(Scanner.Pos, "']' expected");
                                    }
                                }
                                Params(Actual, Formal);
                                if (!EAG.SigOK(HNont))
                                {
                                    Error(Formal.Pos, "formal params differ");
                                }
                                if (Left == '{')
                                {
                                    EAG.NewRep(HNont, HExpr, Formal, Pos);
                                }
                                else
                                {
                                    EAG.NewOpt(HNont, HExpr, Formal, Pos);
                                }
                            }
                        }
                        else
                        {
                            return;
                        }
                    }
                    if (First is null)
                    {
                        First = Last;
                    }
                }
            }

            HExpr = null;
            Last = null;
            while (true)
            {
                Params(Actual, Formal);
                if (!EAG.SigOK(HNont))
                {
                    Error(Formal.Pos, "formal params differ");
                }
                HyperTerm(Actual, FirstF, LastF);
                if (Left == '{' && Actual.Params == EAG.empty)
                {
                    Params(Actual, Formal1);
                    if (Formal1.Params != EAG.empty)
                    {
                        Error(Formal1.Pos, "formal params not allowed here");
                    }
                }
                else if (Left != '{' && Actual.Params != EAG.empty)
                {
                    Error(Actual.Pos, "actual params not allowed here");
                    Actual.Params = EAG.empty;
                }
                EAG.NewAlt(Last, HNont, Formal, Actual, FirstF, LastF, AltPos);
                if (HExpr is null)
                {
                    HExpr = Last;
                }
                if (Tok == '|')
                {
                    AltPos = Scanner.Pos;
                    Scanner.Get(Tok);
                }
                else
                {
                    break;
                }
            }
        }

        HNont = EAG.FindHNont(Id);
        if (!NameNotified && HNont == EAG.firstHNont && ErrorCounter == 0
                && Scanner.ErrorCounter == 0)
        {
            NameNotified = true;
            SetBaseName;
            info!"Analysing %s"(EAG.BaseName);
        }
        EAG.HNont[HNont].IsToken = EAG.HNont[HNont].IsToken || IsToken;
        Params(Actual, Formal);
        if (Actual.Params != EAG.empty)
        {
            Error(Actual.Pos, "actual params not allowed here");
        }
        if (Formal.Params != EAG.empty && EAG.SigOK(HNont))
        {
            Sig = EAG.HNont[HNont].Sig;
            EAG.HNont[HNont].Sig = EAG.empty;
        }
        if (Tok == ':')
        {
            AltPos = Scanner.Pos;
            Scanner.Get(Tok);
        }
        else
        {
            Error(Scanner.Pos, "':' expected");
        }
        HyperExpr(HNont, Id, '(', HExpr, AltPos);
        if (Formal.Params != EAG.empty)
        {
            Distribute(HNont, HExpr, Sig, Formal);
        }
        EAG.NewGrp(HNont, HExpr);
        if (Tok == '.')
        {
            Scanner.Get(Tok);
        }
        else
        {
            Error(Scanner.Pos, "'.' expected");
        }
    }

    Scanner.Get(Tok);
    do
    {
        IsToken = false;
        if (Tok == Scanner.ide)
        {
            Id = Scanner.Val;
            Scanner.Get(Tok);
        }
        else
        {
            Error(Scanner.Pos, "identifier of rule expected");
        }
        if (Tok == Scanner.num)
        {
            Error(Scanner.Pos, "number is not allowed here");
            Scanner.Get(Tok);
        }
        if (Tok == '*')
        {
            IsToken = true;
            Scanner.Get(Tok);
        }
        if (Tok == '=')
        {
            MetaRule(Id, IsToken);
        }
        else
        {
            HyperRule(Id, IsToken);
        }
        if (Tok != Scanner.ide && Tok != Scanner.eot)
        {
            Error(Scanner.Pos, "not allowed symbol");
            do
            {
                Scanner.Get(Tok);
            }
            while (!(Tok == '.' || Tok == Scanner.eot));
            if (Tok != Scanner.eot)
            {
                Scanner.Get(Tok);
            }
            Error(Scanner.Pos, "    restart point");
        }
    }
    while (!(Tok == Scanner.eot));
    ErrorCounter += Scanner.ErrorCounter;
}

void CheckSemantics()
{
    int Sym;
    int n;
    void Shrink()
    {
        EAG.Alt A;
        EAG.Nont F;
        if (EAG.HNont[Sym].Id >= 0 && cast(EAG.Grp) EAG.HNont[Sym].Def !is null)
        {
            A = (cast(EAG.Grp) EAG.HNont[Sym].Def).Sub;
            if (A.Formal.Params == EAG.empty && A.Next is null && A.Sub !is null && cast(EAG.Nont) A.Sub !is null)
            {
                F = cast(EAG.Nont) A.Sub;
                if (EAG.HNont[F.Sym].Id < 0 && F.Actual.Params == EAG.empty && F.Next is null)
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
        EAG.Rule Node;
        EAG.Alt A;
        EAG.Factor F;
        int Sig;

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
                {
                    ++ErrorCounter;
                }
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
                    && cast(EAG.Nont) F.Next !is null
                    && (cast(EAG.Nont) F.Next).Actual.Params == EAG.empty
                    && EAG.HNont[(cast(EAG.Nont) F.Next).Sym].Id < 0)
            {
                (cast(EAG.Nont)F.Next).Actual = F.Actual;
                F.Actual.Params = EAG.empty;
            }
        }

        void CheckRep(EAG.Alt A)
        {
            EAG.Nont F;
            if (A.Last !is null && cast(EAG.Nont) A.Last !is null)
            {
                F = cast(EAG.Nont) A.Last;
                if (EAG.WellMatched(EAG.HNont[F.Sym].Sig, EAG.empty)
                        && F.Actual.Params != EAG.empty
                        && A.Actual.Params == EAG.empty)
                {
                    A.Actual = F.Actual;
                    F.Actual.Params = EAG.empty;
                }
            }
        }

        Node = EAG.HNont[Sym].Def;
        Sig = EAG.HNont[Sym].Sig;
        if (Node !is null)
        {
            if (cast(EAG.Rep) Node !is null)
            {
                EAG.Scope = EAG.NextVar;
                (cast(EAG.Rep) Node).Scope.Beg = EAG.NextVar;
                CheckParamList(Sig, (cast(EAG.Rep) Node).Formal, true);
                (cast(EAG.Rep) Node).Scope.End = EAG.NextVar;
            }
            else if (cast(EAG.Opt) Node !is null)
            {
                EAG.Scope = EAG.NextVar;
                (cast(EAG.Opt) Node).Scope.Beg = EAG.NextVar;
                CheckParamList(Sig, (cast(EAG.Opt) Node).Formal, true);
                (cast(EAG.Opt) Node).Scope.End = EAG.NextVar;
            }
            A = Node.Sub;
            do
            {
                EAG.Scope = EAG.NextVar;
                A.Scope.Beg = EAG.NextVar;
                CheckParamList(Sig, A.Formal, true);
                if (cast(EAG.Rep) Node !is null)
                {
                    CheckRep(A);
                    CheckParamList(Sig, A.Actual, false);
                }
                F = A.Sub;
                while (F !is null)
                {
                    if (cast(EAG.Nont) F !is null)
                    {
                        CheckActual(cast(EAG.Nont) F);
                        CheckParamList(EAG.HNont[(cast(EAG.Nont) F).Sym].Sig, (cast(EAG.Nont) F).Actual, false);
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
    for (Sym = EAG.firstHNont; Sym < EAG.NextHNont; ++Sym)
    {
        if (EAG.HNont[Sym].Def is null)
        {
            if (EAG.HNont[Sym].Id >= 0)
            {
                ++ErrorCounter;
                error!"hyper-nonterminal %s undefined"(Scanner.repr(EAG.HNont[Sym].Id));
            }
        }
        else
        {
            EAG.All[Sym] = true;
            Shrink;
        }
    }
    for (Sym = EAG.firstMNont; Sym < EAG.NextMNont; ++Sym)
    {
        if (EAG.MNont[Sym].MRule == nil)
        {
            ++ErrorCounter;
            error!"meta-nonterminal %s undefined"(Scanner.repr(EAG.MNont[Sym].Id));
        }
    }
    if (ErrorCounter == 0)
    {
        for (Sym = EAG.firstHNont; Sym < EAG.NextHNont; ++Sym)
            Traverse(Sym);
        for (n = EAG.firstVar; n < EAG.NextVar; ++n)
        {
            if (EAG.Var[n].Num < 0 && EAG.Var[n].Neg == EAG.nil)
            {
                Error(EAG.Var[n].Pos, "#-operator not allowed");
            }
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
                    Scanner.repr(EAG.HNont[EAG.StartSym].Id));
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
    int Sym;
    EAG.Alt A;
    EAG.Factor F;
    BitArray Prod;
    long Warnings;
    bool TermFound;

    void ComputeReach(int Sym)
    {
        EAG.Alt A = EAG.HNont[Sym].Def.Sub;
        EAG.Factor F;

        EAG.Reach[Sym] = true;
        do
        {
            F = A.Sub;
            while (F !is null)
            {
                if (cast(EAG.Nont) F !is null && !EAG.Reach[(cast(EAG.Nont) F).Sym])
                {
                    ComputeReach((cast(EAG.Nont) F).Sym);
                }
                F = F.Next;
            }
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

    Warnings = 0;
    EAG.Reach = BitArray();
    EAG.Reach.length = EAG.NextHNont + 1;

    ComputeReach(EAG.StartSym);
    for (Sym = EAG.firstHNont; Sym < EAG.NextHNont; ++Sym)
        if (EAG.HNont[Sym].Def !is null && !EAG.Reach[Sym] && EAG.HNont[Sym].Id >= 0)
            ++Warnings;
    Deg = new int[EAG.NextHAlt];
    Stack = new int[EAG.NextHNont];
    Top = 0;
    Edge = new EdgeRecord[EAG.NextHNont + EAG.NONont + 1];
    NextEdge = EAG.NextHNont;
    for (Sym = EAG.firstHNont; Sym < EAG.NextHNont; ++Sym)
        Edge[Sym].Next = nil;
    EAG.Null = BitArray();
    EAG.Null.length = EAG.NextHNont + 1;
    Prod = BitArray();
    Prod.length = EAG.NextHNont + 1;
    for (Sym = EAG.firstHNont; Sym < EAG.NextHNont; ++Sym)
    {
        if (EAG.HNont[Sym].Def !is null)
        {
            if (cast(EAG.Opt) EAG.HNont[Sym].Def !is null || cast(EAG.Rep) EAG.HNont[Sym].Def !is null)
            {
                Prod[Sym] = true;
                Stack[Top] = Sym;
                ++Top;
            }
            A = EAG.HNont[Sym].Def.Sub;
            do
            {
                TermFound = false;
                Deg[A.Ind] = 0;
                F = A.Sub;
                while (F !is null)
                {
                    if (cast(EAG.Term) F !is null)
                    {
                        TermFound = true;
                    }
                    else
                    {
                        ++Deg[A.Ind];
                        NewEdge((cast(EAG.Nont) F).Sym, A);
                    }
                    F = F.Next;
                }
                if (TermFound)
                {
                    Deg[A.Ind] += int.min;
                }
                else
                {
                    TestDeg(A);
                }
                A = A.Next;
            }
            while (A !is null);
        }
    }
    Prune;
    EAG.Null = Prod.dup;
    for (Sym = EAG.firstHNont; Sym < EAG.NextHNont; ++Sym)
    {
        if (EAG.HNont[Sym].Def !is null)
        {
            A = EAG.HNont[Sym].Def.Sub;
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
    // TODO: foreach (Sym; EAG.All)
    for (Sym = EAG.firstHNont; Sym < EAG.NextHNont; ++Sym)
    {
        if (EAG.All[Sym] && !EAG.Prod[Sym])
            ++Warnings;
    }
    if (Warnings > 0)
        warn!"%s warnings"(Warnings);
}

void Analyse(TextIn textIn)
{
    Scanner.Init(textIn);
    EAG.Init;
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
        info!"OK";
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
{
    if (EAG.Performed(EAG.analysed))
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
                if (EAG.HNont[Sym].Id < 0)
                    warn!"anonymous nonterminal in %s unproductive"(EAG.NamedHNontRepr(Sym));
                else
                    warn!"%s unproductive"(EAG.HNontRepr(Sym));
            }
        }
    }
}

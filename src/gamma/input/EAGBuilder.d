module gamma.input.EAGBuilder;

import epsilon.eag : EAG;
import gamma.grammar.affixes.Composite;
import gamma.grammar.affixes.Direction;
import gamma.grammar.affixes.Signature;
import gamma.grammar.affixes.Term;
import gamma.grammar.affixes.Variable;
import gamma.grammar.Alternative;
import gamma.grammar.GrammarProperties;
import gamma.grammar.hyper.AnonymousNonterminal;
import gamma.grammar.hyper.HyperLhsNode;
import gamma.grammar.hyper.HyperSymbolNode;
import gamma.grammar.hyper.Operator;
import gamma.grammar.hyper.Params;
import gamma.grammar.LhsNode;
import gamma.grammar.Node;
import gamma.grammar.Nonterminal;
import gamma.grammar.Rule;
import gamma.grammar.SymbolNode;
import gamma.grammar.Terminal;
import gamma.input.epsilang.analyzer : GammaEAG = EAG;
import io : Position;
import std.bitmanip : BitArray;
import std.range;
import symbols : SymbolTable;

/**
 * Converts Gamma's validated grammar model into the EAG consumed by epsilon's
 * remaining generator stages.
 */
public EAG toEAG(GammaEAG eag)
{
    return new EAGBuilder(eag).build;
}

private class EAGBuilder
{
    private GammaEAG eag;

    private SymbolTable symbolTable;

    // These buffers use EAG indices directly. Index 0 is unused where the
    // corresponding EAG firstX constant is 1.

    private EAG.MNontRecord[] mNont;   // index 0 unused (EAG.firstMNont = 1)
    private EAG.MTermRecord[] mTerm;   // index 0 unused (EAG.firstMTerm = 1)
    private EAG.MAltRecord[]  mAlt;    // index 0 unused (EAG.firstMAlt  = 1)
    private int[]             membBuf; // index 0 unused (EAG.firstMemb  = 1)
    private int               maxMArity;

    // Symbol-table ID -> EAG index.
    private int[int] mNontById;
    private int[int] mTermById;

    // -------------------------------------------------------------------------
    // Hyper symbols start at index 0 and need no dummy entry.
    // -------------------------------------------------------------------------

    private EAG.HNontRecord[] hNont;
    private EAG.HTermRecord[] hTerm;

    // Every nonterminal object -> its hNont index (covers named and anonymous).
    private int[Nonterminal] hNontByNonterminal;
    // Symbol-table ID -> hTerm index.
    private int[int]         hTermById;

    // Negative IDs distinguish anonymous nonterminals from named symbols.
    private int hNextAnonym = -1;

    // Alternatives and factors have independent dense indices.
    private int nextHAlt    = EAG.firstHAlt;
    private int nextHFactor = EAG.firstHFactor;

    // Grammar properties use the EAG hyper-nonterminal indices.
    private BitArray reachableHNonterminals;
    private BitArray productiveHNonterminals;
    private BitArray nullableHNonterminals;

    // Affix buffers are owned separately so they can be reset together.

    private AffixBuilder affixBuilder;
    private ref int[] domBuf() { return this.affixBuilder.domBuf; }
    private ref int nextDom() { return this.affixBuilder.nextDom; }
    private ref int curSig() { return this.affixBuilder.curSig; }
    private ref EAG.ParamRecord[] paramBuf() { return this.affixBuilder.paramBuf; }
    private ref int nextParam() { return this.affixBuilder.nextParam; }
    private ref int[] nodeBuf() { return this.affixBuilder.nodeBuf; }
    private ref int nextNode() { return this.affixBuilder.nextNode; }
    private ref EAG.VarRecord[] varBuf() { return this.affixBuilder.varBuf; }
    private ref int nextVarBuf() { return this.affixBuilder.nextVarBuf; }
    private ref int currentScope() { return this.affixBuilder.currentScope; }

    // Maps built during hyper-structure construction (used by buildAffixes)
    private Alternative[EAG.Alt]  alternativeByAlt;  // EAG.Alt  → gamma Alternative
    private Rule[int]             ruleByHNontSym;    // hNont idx → grammar Rule
    private Params[int]           endParamsByHNontSym; // hNont idx → endParams of Opt/Rep operator
    private EAG.Nont[size_t]      nontByParamsKey;   // params.key → EAG.Nont factor
    private int[Alternative]      altToGammaMAlt;    // meta Alternative → mAlt index

    this(GammaEAG eag)
    {
        this.eag = eag;
        this.symbolTable = new SymbolTable;

        // Reserve slot 0 in each array so real entries start at index 1
        this.mNont   = new EAG.MNontRecord[1];
        this.mTerm   = new EAG.MTermRecord[1];
        this.mAlt    = new EAG.MAltRecord[1];
        this.membBuf = new int[1];

        buildMeta;
        buildHyper;
        buildAffixes;
        buildSets;
    }

    private EAG build()
    {
        EAG result;

        result.ParamBuf = this.paramBuf[0 .. this.nextParam].dup;
        result.NextParam = this.nextParam;
        result.NodeBuf = this.nodeBuf[0 .. this.nextNode].dup;
        result.NextNode = this.nextNode;
        result.Var = this.varBuf[0 .. this.nextVarBuf].dup;
        result.NextVar = this.nextVarBuf;
        result.Scope = this.currentScope;

        result.DomBuf = this.domBuf[0 .. this.nextDom].dup;
        result.NextDom = this.nextDom;

        result.MAlt = this.mAlt.dup;
        result.NextMAlt = cast(int) result.MAlt.length;
        result.MaxMArity = this.maxMArity;
        result.MembBuf = this.membBuf.dup;
        result.NextMemb = cast(int) result.MembBuf.length;
        result.MTerm = this.mTerm.dup;
        result.NextMTerm = cast(int) result.MTerm.length;
        result.MNont = this.mNont.dup;
        result.NextMNont = cast(int) result.MNont.length;

        result.HTerm = this.hTerm.dup;
        result.NextHTerm = cast(int) result.HTerm.length;
        result.HNont = this.hNont.dup;
        result.NextHNont = cast(int) result.HNont.length;
        result.NextHAlt = this.nextHAlt;
        result.NextHFactor = this.nextHFactor;

        result.All.length = result.NextHNont + 1;
        foreach (nont; 0 .. result.HNont.length)
            result.All[nont] = true;
        result.Reach = this.reachableHNonterminals.withTrailingSlot;
        result.Prod = this.productiveHNonterminals.withTrailingSlot;
        result.Null = this.nullableHNonterminals.withTrailingSlot;

        countNontFactors(result);

        auto startSymbol = this.eag.plainHyperGrammar.startSymbol;
        result.StartSym = this.hNontByNonterminal[startSymbol];
        result.BaseName = startSymbol.toString;

        result.symbolTable = this.symbolTable;
        return result;
    }

    private static void countNontFactors(ref EAG result)
    {
        foreach (hNont; result.HNont)
        {
            if (hNont.Def is null)
                continue;

            for (EAG.Alt alt = hNont.Def.Sub; alt !is null; alt = alt.Next)
                for (EAG.Factor factor = alt.Sub; factor !is null; factor = factor.Next)
                    if (cast(EAG.Nont) factor)
                        ++result.NontCount;
        }
    }

    // =========================================================================
    // Meta rules
    // =========================================================================

    private void buildMeta()
    {
        foreach (rule; this.eag.metaGrammar.rules)
        {
            if (rule is null) continue;
            Nonterminal nonterminal = (cast(LhsNode) rule.lhs).nonterminal;
            const lhsSym = internMNont(nonterminal.toString);

            this.mNont[lhsSym].IsToken = this.mNont[lhsSym].IsToken
                || nonterminal in this.eag.lexicalMetaNonterminals;

            foreach (alternative; rule.alternatives)
            {
                const rhs = cast(int) this.membBuf.length;

                this.altToGammaMAlt[alternative] = cast(int) this.mAlt.length;

                foreach (node; alternative.rhs)
                {
                    auto symbolNode = cast(SymbolNode) node;
                    auto symbol = symbolNode.symbol;

                    if (cast(Nonterminal) symbol)
                        this.membBuf ~= internMNont(symbol.toString);
                    else
                        this.membBuf ~= -internMTerm(symbol.toString);
                }
                this.membBuf ~= EAG.nil; // end-of-alternative sentinel
                appendMAlt(lhsSym, rhs);
            }
        }
    }

    // =========================================================================
    // Hyper grammar
    // =========================================================================

    private void buildHyper()
    {
        if (this.eag.hyperEBNFGrammar is null)
            return;

        // A direct named EBNF definition uses the operator alternatives at the
        // named nonterminal, so its generated anonymous helper is omitted.
        bool[Nonterminal] omittedDirectOperatorHelpers;

        foreach (rule; this.eag.hyperEBNFGrammar.rules)
            if (auto op = rule.directNamedOperator)
                omittedDirectOperatorHelpers[op.rule.lhs.nonterminal] = true;

        // Pre-populate HNont entries in source order so anonymous IDs are stable.
        foreach (nonterminal; this.eag.hyperEBNFGrammar.nonterminals)
            if (nonterminal !in omittedDirectOperatorHelpers)
                findOrCreateHNont(nonterminal);

        // Walk only named rules; anonymous nonterminal rules are embedded in
        // operator nodes and processed recursively by buildHyperFactor.
        foreach (rule; this.eag.hyperEBNFGrammar.rules)
        {
            if (rule is null) continue;

            Nonterminal nonterminal = rule.lhs.nonterminal;
            const int   gammaSym   = findOrCreateHNont(nonterminal);
            this.ruleByHNontSym[gammaSym] = rule;

            this.hNont[gammaSym].IsToken =
                this.hNont[gammaSym].IsToken ||
                (nonterminal in this.eag.lexicalHyperNonterminals) !is null;

            if (auto op = rule.directNamedOperator)
            {
                buildDirectOperatorDefinition(gammaSym, op);
                continue;
            }

            EAG.Alt firstAlt = null;
            EAG.Alt lastAlt  = null;

            foreach (alternative; rule.alternatives)
                buildHyperAlt(gammaSym, alternative, firstAlt, lastAlt);

            if (this.hNont[gammaSym].Def is null)
            {
                auto grp = new EAG.Grp;

                grp.Sub = firstAlt;
                this.hNont[gammaSym].Def = grp;
            }
            else
            {
                // Append to existing Grp (same name, multiple source rules).
                EAG.Alt a = this.hNont[gammaSym].Def.Sub;

                while (a !is null && a.Next !is null)
                    a = a.Next;
                if (a !is null)
                    a.Next = firstAlt;
            }
        }
    }

    private void buildHyperAlt(int lhsSym, Alternative alternative,
                                ref EAG.Alt firstAlt, ref EAG.Alt lastAlt)
    {
        EAG.Factor firstFactor = null;
        EAG.Factor lastFactor  = null;

        foreach (node; alternative.rhs)
            buildHyperFactor(node, firstFactor, lastFactor);

        auto alt = new EAG.Alt;

        alt.Up        = lhsSym;
        alt.Sub       = firstFactor;
        alt.Last      = lastFactor;
        alt.Formal    = EAG.ParamsDesc.init;
        alt.Actual    = EAG.ParamsDesc.init;
        alt.Scope.Beg = EAG.nil;
        alt.Scope.End = EAG.nil;
        alt.Pos       = alternative.position;
        alt.Ind       = this.nextHAlt++;
        alt.Next      = null;

        this.alternativeByAlt[alt] = alternative;

        if (firstAlt is null)
            firstAlt = alt;
        else
            lastAlt.Next = alt;
        lastAlt = alt;
    }

    private void buildHyperFactor(Node node, ref EAG.Factor firstFactor, ref EAG.Factor lastFactor)
    {
        import gamma.grammar.hyper.Group      : HyperGroup = Group;
        import gamma.grammar.hyper.Option     : HyperOption = Option;
        import gamma.grammar.hyper.Repetition : HyperRepetition = Repetition;

        if (auto grp = cast(HyperGroup) node)
        {
            const sym = findOrCreateHNont(grp.rule.lhs.nonterminal);

            buildHyperGrpDefinition(sym, grp.rule);
            appendHNont(firstFactor, lastFactor, sym, grp.position);
            if (grp.params !is null)
                this.nontByParamsKey[grp.params.key] = cast(EAG.Nont) lastFactor;
        }
        else if (auto opt = cast(HyperOption) node)
        {
            const anonSym = findOrCreateHNont(opt.rule.lhs.nonterminal);

            buildHyperOptDefinition(anonSym, opt.rule, opt.position);
            appendHNont(firstFactor, lastFactor, anonSym, opt.position);
            if (opt.params !is null)
                this.nontByParamsKey[opt.params.key] = cast(EAG.Nont) lastFactor;
            if (opt.endParams !is null)
                this.endParamsByHNontSym[anonSym] = opt.endParams;
        }
        else if (auto rep = cast(HyperRepetition) node)
        {
            const anonSym = findOrCreateHNont(rep.rule.lhs.nonterminal);

            buildHyperRepDefinition(anonSym, rep.rule, rep.position);
            appendHNont(firstFactor, lastFactor, anonSym, rep.position);
            if (rep.params !is null)
                this.nontByParamsKey[rep.params.key] = cast(EAG.Nont) lastFactor;
            if (rep.endParams !is null)
                this.endParamsByHNontSym[anonSym] = rep.endParams;
        }
        else if (auto sn = cast(SymbolNode) node)
        {
            if (cast(Terminal) sn.symbol)
                appendHTerm(firstFactor, lastFactor,
                    findOrCreateHTerm(sn.symbol.toString), sn.position);
            else
            {
                appendHNont(firstFactor, lastFactor,
                    findOrCreateHNont(cast(Nonterminal) sn.symbol), sn.position);
                if (auto hsn = cast(HyperSymbolNode) sn)
                    if (hsn.params !is null)
                        this.nontByParamsKey[hsn.params.key] = cast(EAG.Nont) lastFactor;
            }
        }
    }

    private void buildDirectOperatorDefinition(int target, Operator op)
    {
        import gamma.grammar.hyper.Group      : HyperGroup = Group;
        import gamma.grammar.hyper.Option     : HyperOption = Option;
        import gamma.grammar.hyper.Repetition : HyperRepetition = Repetition;

        if (auto group = cast(HyperGroup) op)
            buildHyperGrpDefinition(target, group.rule);
        else if (auto option = cast(HyperOption) op)
        {
            buildHyperOptDefinition(target, option.rule, option.position);
            if (option.endParams !is null)
                this.endParamsByHNontSym[target] = option.endParams;
        }
        else if (auto repetition = cast(HyperRepetition) op)
        {
            buildHyperRepDefinition(target, repetition.rule, repetition.position);
            if (repetition.endParams !is null)
                this.endParamsByHNontSym[target] = repetition.endParams;
        }
        else
            assert(false, "unknown EBNF operator");
    }

    private void buildHyperGrpDefinition(int target, Rule rule)
    {
        EAG.Alt firstAlt = null;
        EAG.Alt lastAlt  = null;

        this.ruleByHNontSym[target] = rule;

        foreach (alternative; rule.alternatives)
            buildHyperAlt(target, alternative, firstAlt, lastAlt);

        auto grp = new EAG.Grp;

        grp.Sub = firstAlt;
        this.hNont[target].Def = grp;
    }

    private void buildHyperOptDefinition(int target, Rule rule, Position position)
    {
        EAG.Alt firstAlt = null;
        EAG.Alt lastAlt  = null;

        this.ruleByHNontSym[target] = rule;

        foreach (alternative; rule.alternatives)
            buildHyperAlt(target, alternative, firstAlt, lastAlt);

        auto opt = new EAG.Opt;

        opt.Sub         = firstAlt;
        opt.EmptyAltPos = position;
        opt.Scope.Beg   = EAG.nil;
        opt.Scope.End   = EAG.nil;
        opt.Formal      = EAG.ParamsDesc.init;
        this.hNont[target].Def = opt;
    }

    private void buildHyperRepDefinition(int target, Rule rule, Position position)
    {
        EAG.Alt firstAlt = null;
        EAG.Alt lastAlt  = null;

        this.ruleByHNontSym[target] = rule;

        foreach (alternative; rule.alternatives)
            buildHyperAlt(target, alternative, firstAlt, lastAlt);

        auto rep = new EAG.Rep;

        rep.Sub         = firstAlt;
        rep.EmptyAltPos = position;
        rep.Scope.Beg   = EAG.nil;
        rep.Scope.End   = EAG.nil;
        rep.Formal      = EAG.ParamsDesc.init;
        this.hNont[target].Def = rep;
    }

    // =========================================================================
    // Affix data
    // =========================================================================

    private void buildAffixes()
    {
        import gamma.grammar.hyper.RepetitionAlternative : RepetitionAlternative;

        if (this.eag.hyperEBNFGrammar is null)
            return;

        this.affixBuilder.reset;

        // Build every signature before parameters so forward references can
        // resolve the direction of each actual parameter.
        foreach (gammaSym; EAG.firstHNont .. cast(int) this.hNont.length)
        {
            if (this.hNont[gammaSym].Def is null)
                continue;

            Rule rule = this.ruleByHNontSym.get(gammaSym, null);

            if (rule is null)
                continue;

            this.hNont[gammaSym].Sig = buildAffixSig(gammaSym, rule);
        }

        // Build parameters and variables one alternative scope at a time.
        foreach (gammaSym; EAG.firstHNont .. cast(int) this.hNont.length)
        {
            if (this.hNont[gammaSym].Def is null)
                continue;

            Rule rule = this.ruleByHNontSym.get(gammaSym, null);

            if (rule is null)
                continue;

            int sig = this.hNont[gammaSym].Sig;

            // --- Rep/Opt: build Formal ParamsDesc + Scope ---
            if (auto rep = cast(EAG.Rep) this.hNont[gammaSym].Def)
            {
                this.currentScope = this.nextVarBuf;
                rep.Scope.Beg      = this.nextVarBuf;
                Params endP = this.endParamsByHNontSym.get(gammaSym, null);
                if (endP !is null)
                {
                    auto terms = this.eag.hyperEBNFGrammar.terms(endP.key);
                    rep.Formal = buildAffixTermsParamsDesc(terms, sig, true, endP.position);
                }
                rep.Scope.End = this.nextVarBuf;
            }
            else if (auto opt = cast(EAG.Opt) this.hNont[gammaSym].Def)
            {
                this.currentScope = this.nextVarBuf;
                opt.Scope.Beg      = this.nextVarBuf;
                Params endP = this.endParamsByHNontSym.get(gammaSym, null);
                if (endP !is null)
                {
                    auto terms = this.eag.hyperEBNFGrammar.terms(endP.key);
                    opt.Formal = buildAffixTermsParamsDesc(terms, sig, true, endP.position);
                }
                opt.Scope.End = this.nextVarBuf;
            }

            // --- Walk each Alt ---
            for (EAG.Alt gammaAlt = this.hNont[gammaSym].Def.Sub;
                 gammaAlt !is null;
                 gammaAlt = gammaAlt.Next)
            {
                Alternative alternative = this.alternativeByAlt.get(gammaAlt, null);

                if (alternative is null)
                    continue;

                this.currentScope   = this.nextVarBuf;
                gammaAlt.Scope.Beg  = this.nextVarBuf;

                // Formal params on the Alt lhs
                gammaAlt.Formal = buildAffixLhsParamsDesc(
                    alternative.lhs, sig, true, alternative.position);

                // A trailing parameter list can belong either to the repetition
                // alternative or to its last symbol. Matching keys identify the
                // latter case; every other list is the alternative's actual list.
                bool repActualIsUndecided = false;

                if (auto repAlt = cast(RepetitionAlternative) alternative)
                {
                    if (repAlt.params !is null)
                    {
                        if (!alternative.rhs.empty)
                        {
                            import gamma.grammar.hyper.HyperSymbolNode : HyperSymbolNode;

                            if (auto lastHsn = cast(HyperSymbolNode) alternative.rhs.back)
                                if (lastHsn.params !is null
                                    && lastHsn.params.key == repAlt.params.key)
                                    repActualIsUndecided = true;
                        }

                        if (!repActualIsUndecided)
                        {
                            auto terms = this.eag.hyperEBNFGrammar.terms(repAlt.params.key);
                            gammaAlt.Actual = buildAffixTermsParamsDesc(terms, sig, false,
                                repAlt.params.position);
                        }
                    }
                }

                // Walk factors in parallel with alternative.rhs
                EAG.Factor f = gammaAlt.Sub;

                foreach (node; alternative.rhs)
                {
                    if (f is null)
                        break;

                    if (auto nont = cast(EAG.Nont) f)
                        buildAffixNontFactor(nont, node);

                    f = f.Next;
                }

                gammaAlt.Scope.End = this.nextVarBuf;
            }
        }
    }

    // Append a nil-terminated DomBuf signature and return its start index.
    private int buildAffixSig(int gammaSym, Rule rule)
    {
        Signature signature = this.eag.hyperEBNFGrammar.signatureOf(rule.lhs.nonterminal);

        if (signature !is null && !signature.isEmpty)
        {
            foreach (i, dir; signature.direction)
            {
                const mNontSym = internMNont(signature.domains[i].toString);
                this.domBuf ~= (dir == Direction.output) ? mNontSym : -mNontSym;
                ++this.nextDom;
            }
        }
        return affixSigOk(gammaSym);
    }

    // Seals the current DomBuf sequence and sets HNont.Sig.
    private int affixSigOk(int gammaSym)
    {
        if (this.hNont[gammaSym].Sig < 0)
        {
            // First call: record the start of this signature sequence.
            this.hNont[gammaSym].Sig = this.curSig;
            this.domBuf ~= EAG.nil;
            ++this.nextDom;
            this.curSig = this.nextDom;
        }
        else
        {
            // Subsequent call: discard tentative entries (reset back to curSig).
            this.domBuf.length = this.curSig;
            this.nextDom = this.curSig;
        }
        return this.hNont[gammaSym].Sig;
    }

    // Build a ParamsDesc from a LhsNode reference (for Alt.lhs dispatch).
    private EAG.ParamsDesc buildAffixLhsParamsDesc(
        LhsNode lhsNode, int sig, bool isLhs, Position fallbackPos)
    {
        auto hln = cast(HyperLhsNode) lhsNode;

        if (hln is null || hln.params is null)
            return EAG.ParamsDesc(EAG.empty, fallbackPos);

        auto terms = this.eag.hyperEBNFGrammar.terms(hln.params.key);

        return buildAffixTermsParamsDesc(terms, sig, isLhs, hln.params.position);
    }

    // Build a ParamsDesc from a Term[] slice (already Earley-parsed).
    private EAG.ParamsDesc buildAffixTermsParamsDesc(
        Term[] terms, int sig, bool isLhs, Position pos)
    {
        if (terms.length == 0)
            return EAG.ParamsDesc(EAG.empty, pos);

        const startParam = this.nextParam;

        foreach (i, term; terms)
        {
            const bool isDef = affixIsDef(sig, cast(int) i, isLhs);
            const int  tree  = buildAffixTerm(term, isDef);

            this.paramBuf ~= EAG.ParamRecord(tree, pos, isDef);
            ++this.nextParam;
        }
        // Nil terminator
        this.paramBuf ~= EAG.ParamRecord(EAG.nil, pos, false);
        ++this.nextParam;

        return EAG.ParamsDesc(startParam, pos);
    }

    // Formal inputs and actual outputs define their variables.
    private bool affixIsDef(int sig, int index, bool isLhs)
    {
        if (sig < 0 || sig >= cast(int) this.domBuf.length)
            return false;

        int dom = sig;
        int i   = 0;

        while (this.domBuf[dom] != EAG.nil && i < index)
        {
            ++dom;
            ++i;
        }
        if (this.domBuf[dom] == EAG.nil)
            return false;

        const int entry = this.domBuf[dom];

        return isLhs ? entry < 0 : entry > 0;
    }

    // Translate a Term tree to a NodeBuf/VarBuf reference.
    // Composite roots use non-negative NodeBuf indices; variables use negative
    // VarBuf indices.
    private int buildAffixTerm(Term term, bool isDef)
    {
        if (auto v = cast(Variable) term)
        {
            const mNontSym = internMNont(v.nonterminal.toString);
            int   num;

            if (v.number.isNull)
            {
                num = v.unequal ? -1 : 1;
            }
            else
            {
                const sign = v.unequal ? -1 : 1;
                // Number suffixes use their symbol-table ID plus two; the sign
                // distinguishes an unequal variable from its positive partner.
                num = sign * (cast(int) this.symbolTable.intern(v.number.get) + 2);
            }

            return -affixFindOrCreateVar(mNontSym, num, v.position, isDef);
        }

        auto c = cast(Composite) term;

        assert(c !is null, "Term must be Variable or Composite");

        const gammaMAltIdx = this.altToGammaMAlt.get(c.alternative, 0);
        const treeIndex    = this.nextNode;

        assert(gammaMAltIdx > EAG.nil);
        assert(c.terms.length == this.mAlt[gammaMAltIdx].Arity);

        // NodeBuf stores a composite's child roots immediately after its root.
        // Reserve those slots before recursively emitting a child: a nested
        // composite otherwise places its own subtree between two parent slots.
        this.nodeBuf.length = this.nextNode + c.terms.length + 1;
        this.nodeBuf[treeIndex] = gammaMAltIdx;
        this.nextNode += c.terms.length + 1;

        foreach (i, sub; c.terms)
        {
            const childTree = buildAffixTerm(sub, isDef);

            assert(childTree != EAG.nil);
            this.nodeBuf[treeIndex + i + 1] = childTree;
        }
        return treeIndex;
    }

    // Looks up or creates a VarRecord for (sym, num).
    // within the current scope [currentScope .. nextVarBuf).
    private int affixFindOrCreateVar(int sym, int num, Position pos, bool isDef)
    {
        // Search from current scope start.
        for (int v = this.currentScope; v < this.nextVarBuf; ++v)
        {
            if (this.varBuf[v].Sym == sym && this.varBuf[v].Num == num)
            {
                this.varBuf[v].Def = this.varBuf[v].Def || isDef;
                return v;
            }
        }
        // Also check for the negated partner (Neg linkage).
        for (int v = this.currentScope; v < this.nextVarBuf; ++v)
        {
            if (this.varBuf[v].Sym == sym && this.varBuf[v].Num == -num)
            {
                // Negated partner found — link.
                const int newV = this.nextVarBuf;

                this.varBuf ~= EAG.VarRecord(sym, num, v, pos, isDef);
                this.varBuf[v].Neg     = newV;
                ++this.nextVarBuf;
                return newV;
            }
        }
        // New variable.
        const int newV = this.nextVarBuf;

        this.varBuf ~= EAG.VarRecord(sym, num, EAG.nil, pos, isDef);
        ++this.nextVarBuf;
        return newV;
    }

    // Process actual params for a nonterminal RHS factor.
    // `node` is the grammar RHS node (HyperSymbolNode or Operator).
    private void buildAffixNontFactor(EAG.Nont nont, Node node)
    {
        import gamma.grammar.hyper.Group      : HyperGroup = Group;
        import gamma.grammar.hyper.Operator   : Operator;
        import gamma.grammar.hyper.Option     : HyperOption = Option;
        import gamma.grammar.hyper.Repetition : HyperRepetition = Repetition;

        const refSig = this.hNont[nont.Sym].Sig;

        if (auto hsn = cast(HyperSymbolNode) node)
        {
            if (hsn.params !is null)
            {
                auto terms = this.eag.hyperEBNFGrammar.terms(hsn.params.key);

                nont.Actual = buildAffixTermsParamsDesc(terms, refSig, false,
                    hsn.params.position);
            }
        }
        else if (auto op = cast(Operator) node)
        {
            // Actual params placed before the operator bracket (op.params)
            if (op.params !is null)
            {
                auto terms = this.eag.hyperEBNFGrammar.terms(op.params.key);

                nont.Actual = buildAffixTermsParamsDesc(terms, refSig, false,
                    op.params.position);
            }
        }
    }

    // =========================================================================
    // EAG sets
    // =========================================================================

    private void buildSets()
    {
        if (this.eag.plainHyperGrammar is null)
            return;

        auto grammar = this.eag.plainHyperGrammar;
        auto lexicalNonterminals = this.eag.lexicalHyperNonterminals;
        auto properties = new GrammarProperties(grammar, lexicalNonterminals);

        this.reachableHNonterminals.length = this.hNont.length;
        this.productiveHNonterminals.length = this.hNont.length;
        this.nullableHNonterminals.length = this.hNont.length;

        foreach (nonterminal; this.eag.plainHyperGrammar.nonterminals)
        {
            const gammaSym = this.hNontByNonterminal.get(nonterminal, int.min);

            if (gammaSym == int.min || this.hNont[gammaSym].Def is null)
                continue;

            this.reachableHNonterminals[gammaSym] = properties.isReachable(nonterminal);
            this.productiveHNonterminals[gammaSym] = properties.isProductive(nonterminal);
            this.nullableHNonterminals[gammaSym] = properties.isNullable(nonterminal);
        }
    }

    // =========================================================================
    // Private helpers
    // =========================================================================

    private int internMNont(string name) @safe
    {
        const id = cast(int) this.symbolTable.intern(name);

        if (auto p = id in this.mNontById)
            return *p;

        const sym = cast(int) this.mNont.length;

        this.mNont ~= EAG.MNontRecord(id, EAG.nil, EAG.nil, false);
        this.mNontById[id] = sym;
        return sym;
    }

    private int internMTerm(string name) @safe
    {
        const id = cast(int) this.symbolTable.intern(name);

        if (auto p = id in this.mTermById)
            return *p;

        const sym = cast(int) this.mTerm.length;

        this.mTerm ~= EAG.MTermRecord(id);
        this.mTermById[id] = sym;
        return sym;
    }

    private void appendMAlt(int sym, int right)
    {
        const index = cast(int) this.mAlt.length;
        int arity = 0;

        for (int i = right; this.membBuf[i] != 0; ++i)
            if (this.membBuf[i] > 0)
                ++arity;

        if (arity > this.maxMArity)
            this.maxMArity = arity;

        if (this.mNont[sym].MRule == EAG.nil)
            this.mNont[sym].MRule = index;
        else
            this.mAlt[this.mNont[sym].Last].Next = index;
        this.mNont[sym].Last = index;

        this.mAlt ~= EAG.MAltRecord(sym, right, arity, EAG.nil);
        // The alternative index follows its nil-terminated member sequence.
        this.membBuf ~= index;
    }

    // -------------------------------------------------------------------------
    // Hyper grammar helpers
    // -------------------------------------------------------------------------

    /**
     * Find (or create) the builder's HNont entry for the given gamma nonterminal.
     * Named nonterminals are keyed by their symbolTable Id.
     * Anonymous nonterminals use decreasing negative IDs.
     */
    private int findOrCreateHNont(Nonterminal nonterminal)
    {
        if (auto p = nonterminal in this.hNontByNonterminal)
            return *p;

        const sym = cast(int) this.hNont.length;

        this.hNontByNonterminal[nonterminal] = sym;

        if (cast(AnonymousNonterminal) nonterminal)
        {
            const id = this.hNextAnonym--;

            this.hNont ~= EAG.HNontRecord(id, EAG.nil, -1, null, false);
        }
        else
        {
            // Named: use the shared symbolTable Id.
            const id = cast(int) this.symbolTable.intern(nonterminal.toString);

            this.hNont ~= EAG.HNontRecord(id, id, -1, null, false);
        }
        return sym;
    }

    /**
     * Find (or create) the builder's HTerm entry for the given terminal name.
     */
    private int findOrCreateHTerm(string name)
    {
        const id = cast(int) this.symbolTable.intern(name);

        if (auto p = id in this.hTermById)
            return *p;

        const sym = cast(int) this.hTerm.length;

        this.hTerm ~= EAG.HTermRecord(id);
        this.hTermById[id] = sym;
        return sym;
    }

    /**
     * Append a terminal Factor to the current factor chain.
     * firstFactor is set on the first call; lastFactor always points to the new node.
     */
    private void appendHTerm(ref EAG.Factor firstFactor, ref EAG.Factor lastFactor,
        int sym, Position pos)
    {
        auto f = new EAG.Term;

        f.Sym  = sym;
        f.Pos  = pos;
        f.Ind  = this.nextHFactor++;
        f.Next = null;
        f.Prev = lastFactor;

        if (lastFactor !is null)
            lastFactor.Next = f;
        lastFactor = f;

        if (firstFactor is null)
            firstFactor = f;
    }

    /**
     * Append a nonterminal Factor to the current factor chain.
     */
    private void appendHNont(ref EAG.Factor firstFactor, ref EAG.Factor lastFactor,
        int sym, Position pos)
    {
        auto f = new EAG.Nont;

        f.Sym    = sym;
        f.Actual = EAG.ParamsDesc.init; // Filled during affix construction.
        f.Pos    = pos;
        f.Ind    = this.nextHFactor++;
        f.Next   = null;
        f.Prev   = lastFactor;

        if (lastFactor !is null)
            lastFactor.Next = f;
        lastFactor = f;

        if (firstFactor is null)
            firstFactor = f;
    }
}

private BitArray withTrailingSlot(const BitArray source)
{
    auto result = source.dup;

    result.length = result.length + 1;
    return result;
}

@("EAG sets reserve trailing slot")
unittest
{
    // EAG sets reserve one trailing slot for generator work arrays.
    BitArray source;

    source.length = 2;
    source[0] = true;

    auto target = source.withTrailingSlot;

    assert(target.length == 3);
    assert(target[0]);
    assert(!target[1]);
    assert(!target[2]);
}

/**
 * Owns the affix buffers so they can be reset as one unit.
 */
private struct AffixBuilder
{
    int[] domBuf;
    int nextDom;
    int curSig;
    EAG.ParamRecord[] paramBuf;
    int nextParam;
    int[] nodeBuf;
    int nextNode;
    EAG.VarRecord[] varBuf;
    int nextVarBuf;
    int currentScope;

    void reset()
    {
        this.domBuf = [EAG.nil];
        this.nextDom = 1;
        this.curSig = 1;
        this.paramBuf.length = 1;
        this.paramBuf[0].Affixform = EAG.nil;
        this.nextParam = 1;
        this.nodeBuf = [EAG.nil];
        this.nextNode = EAG.firstNode;
        this.varBuf.length = 1;
        this.nextVarBuf = EAG.firstVar;
        this.currentScope = EAG.firstVar;
    }
}


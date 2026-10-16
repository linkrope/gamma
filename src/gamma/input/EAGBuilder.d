module gamma.input.EAGBuilder;

import epsilon.eag;
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
import log;
import std.bitmanip : BitArray;
import std.format : format;
import std.range;

/**
 * Transforms gamma's validated Grammar models into epsilon's EAG global arrays.
 *
 * Each sub-domain (meta rules, hyper grammar, affixes, sets) has two methods:
 *   buildX(...)   — fills the builder's own internal mirror arrays from the gamma model
 *   compareX()    — diffs those mirrors against the live EAG globals (populated by
 *                   epsilon.analyzer.Analyse) and reports per-field mismatches
 *
 * Because epsilon.analyzer still runs first in main.d the comparison executes
 * automatically on every `dub test --build=unittest --config=example` invocation.
 */
class EAGBuilder
{
    private GammaEAG gammaEAG;

    // Internal mirrors — plain D dynamic arrays.  The Oberon fixed-size buffer
    // + Expand pattern is unnecessary here; D arrays grow automatically.
    // Index 0 of each array is an unused dummy slot to match epsilon's
    // firstX = 1 convention; real entries start at index 1.

    private EAG.MNontRecord[] mNont;   // index 0 unused (EAG.firstMNont = 1)
    private EAG.MTermRecord[] mTerm;   // index 0 unused (EAG.firstMTerm = 1)
    private EAG.MAltRecord[]  mAlt;    // index 0 unused (EAG.firstMAlt  = 1)
    private int[]             membBuf; // index 0 unused (EAG.firstMemb  = 1)
    private int               maxMArity;

    // Lookup maps replacing the Oberon sentinel linear-scan trick
    private int[int] mNontById; // Epsilon symbol-table ID -> mNont index
    private int[int] mTermById; // Epsilon symbol-table ID -> mTerm index

    // -------------------------------------------------------------------------
    // Hyper grammar mirrors — firstHNont = 0, firstHTerm = 0 (no dummy slot 0)
    // -------------------------------------------------------------------------

    private EAG.HNontRecord[] hNont;          // hNont[i] mirrors epsilon HNont[i]
    private EAG.HTermRecord[] hTerm;          // hTerm[i] mirrors epsilon HTerm[i]

    // Named: symbolTable Id -> hNont index.  Anonymous: not tracked here.
    private int[int]         hNontById;
    // Every nonterminal object -> its hNont index (covers named and anonymous).
    private int[Nonterminal] hNontByNonterminal;
    // HTerm: symbolTable Id -> hTerm index.
    private int[int]         hTermById;

    // Anonymous counter: starts at -1 and decrements, matching epsilon's NextAnonym.
    private int hNextAnonym = -1;

    // Anonymous hNont indices in encounter order (for compareHyper bijection).
    private int[] hAnonymNonts;

    // Counters matching epsilon's NextHAlt / NextHFactor.
    private int nextHAlt    = EAG.firstHAlt;
    private int nextHFactor = EAG.firstHFactor;

    // Mirrors epsilon's Reach, Prod, and Null sets.
    private BitArray reachableHNonterminals;
    private BitArray productiveHNonterminals;
    private BitArray nullableHNonterminals;

    // Affix-data mirror.

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

    public this(GammaEAG gammaEAG)
    {
        this.gammaEAG = gammaEAG;

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

    /**
     * Diff the builder's internal meta-grammar mirrors against the live EAG globals
     * (already populated by epsilon.analyzer.Analyse()) and log per-field mismatches.
     *
     * Returns: number of differences found (0 = perfect match)
     */
    public int compare()
    {
        return compareMeta + compareHyper + compareAffixes + compareSets;
    }

    // =========================================================================
    // Meta rules
    // =========================================================================

    private void buildMeta()
    {
        foreach (rule; this.gammaEAG.metaGrammar.rules)
        {
            if (rule is null) continue;
            Nonterminal nonterminal = (cast(LhsNode) rule.lhs).nonterminal;
            const lhsSym = internMNont(nonterminal.toString);

            this.mNont[lhsSym].IsToken = this.mNont[lhsSym].IsToken
                || nonterminal in this.gammaEAG.lexicalMetaNonterminals;

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

    private int compareMeta()
    {
        int count = 0;

        // Build Id→index maps for epsilon's MNont and MTerm entries.
        // Epsilon's symbol table is shared with Gamma: intern() returns the same ID
        // for the same string regardless of call order, so Ids are stable across
        // both traversals and serve as a reliable join key.
        int[int] mNontByIdMap;

        foreach (sym; EAG.firstMNont .. eag.NextMNont)
            mNontByIdMap[eag.MNont[sym].Id] = sym;

        int[int] mTermByIdMap;

        foreach (sym; EAG.firstMTerm .. eag.NextMTerm)
            mTermByIdMap[eag.MTerm[sym].Id] = sym;

        // Bijection maps: gamma index → epsilon index
        int[int] gammaToMNont;

        foreach (gammaSym; EAG.firstMNont .. cast(int) this.mNont.length)
        {
            if (auto p = this.mNont[gammaSym].Id in mNontByIdMap)
                gammaToMNont[gammaSym] = *p;
            else
            {
                error!"compareMeta: MNont '%s' not found in EAG"(
                    eag.symbolTable.symbol(this.mNont[gammaSym].Id));
                ++count;
            }
        }

        int[int] gammaToMTerm;

        foreach (gammaSym; EAG.firstMTerm .. cast(int) this.mTerm.length)
        {
            if (auto p = this.mTerm[gammaSym].Id in mTermByIdMap)
                gammaToMTerm[gammaSym] = *p;
            else
            {
                error!"compareMeta: MTerm '%s' not found in EAG"(
                    eag.symbolTable.symbol(this.mTerm[gammaSym].Id));
                ++count;
            }
        }

        // Compare IsToken and the alternative chains for each nonterminal.
        // Both chains are ordered by the appearance of alternatives in the source,
        // so a parallel walk compares them structurally.
        foreach (gammaSym; EAG.firstMNont .. cast(int) this.mNont.length)
        {
            const symP = gammaSym in gammaToMNont;

            if (!symP)
                continue; // already reported above

            const sym = *symP;
            const symName = eag.symbolTable.symbol(this.mNont[gammaSym].Id);

            if (this.mNont[gammaSym].IsToken != eag.MNont[sym].IsToken)
            {
                error!"compareMeta: MNont '%s' IsToken %s != %s"(
                    symName,
                    this.mNont[gammaSym].IsToken, eag.MNont[sym].IsToken);
                ++count;
            }

            int gammaAlt = this.mNont[gammaSym].MRule;
            int alt      = eag.MNont[sym].MRule;

            while (gammaAlt != EAG.nil || alt != EAG.nil)
            {
                if (gammaAlt == EAG.nil || alt == EAG.nil)
                {
                    error!"compareMeta: MNont '%s' alternative count differs"(symName);
                    ++count;
                    break;
                }

                // Compare member sequences up to the nil sentinel.
                // The self-reference entry that follows nil is skipped.
                int gammaI = this.mAlt[gammaAlt].Right;
                int i      = eag.MAlt[alt].Right;

                while (this.membBuf[gammaI] != EAG.nil || eag.MembBuf[i] != EAG.nil)
                {
                    if (this.membBuf[gammaI] == EAG.nil || eag.MembBuf[i] == EAG.nil)
                    {
                        error!"compareMeta: MNont '%s' alternative member count differs"(symName);
                        ++count;
                        break;
                    }

                    const gammaVal = this.membBuf[gammaI];
                    const val      = eag.MembBuf[i];

                    // Translate gamma index to epsilon index using the bijection.
                    // Positive values are MNont refs; negative are MTerm refs.
                    int translated;

                    if (gammaVal > 0)
                        translated = gammaToMNont.get(gammaVal, int.min);
                    else
                    {
                        const t = gammaToMTerm.get(-gammaVal, int.min);

                        translated = (t == int.min) ? int.min : -t;
                    }

                    if (translated != val)
                    {
                        const gammaName = gammaVal > 0
                            ? eag.symbolTable.symbol(this.mNont[gammaVal].Id)
                            : eag.symbolTable.symbol(this.mTerm[-gammaVal].Id);

                        error!"compareMeta: MNont '%s' alt member: gamma '%s' maps to %s, expected %s"(
                            symName, gammaName, translated, val);
                        ++count;
                    }

                    ++gammaI;
                    ++i;
                }

                gammaAlt = this.mAlt[gammaAlt].Next;
                alt      = eag.MAlt[alt].Next;
            }
        }

        // Epsilon may create extra MNont entries for domain references in hyper
        // rules; report only when the builder has more.
        if (cast(int) this.mNont.length > eag.NextMNont)
        {
            error!"compareMeta: builder has %s MNont entries but EAG only has %s"(
                this.mNont.length - EAG.firstMNont, eag.NextMNont - EAG.firstMNont);
            ++count;
        }

        if (cast(int) this.mTerm.length != eag.NextMTerm)
        {
            error!"compareMeta: builder has %s MTerm entries but EAG has %s"(
                this.mTerm.length - EAG.firstMTerm, eag.NextMTerm - EAG.firstMTerm);
            ++count;
        }

        if (count == 0)
            trace!"compareMeta: OK";
        return count;
    }

    // =========================================================================
    // Hyper grammar
    // =========================================================================

    private void buildHyper()
    {
        if (this.gammaEAG.hyperEBNFGrammar is null)
            return;

        // epsilon's Shrink() removes the generated helper of a direct named
        // EBNF definition.  Keep Gamma's source model intact, but omit that
        // helper from this legacy projection.
        bool[Nonterminal] omittedDirectOperatorHelpers;

        foreach (rule; this.gammaEAG.hyperEBNFGrammar.rules)
            if (auto op = rule.directOperator)
                omittedDirectOperatorHelpers[op.rule.lhs.nonterminal] = true;

        // Pre-populate the projected hNont entries in source encounter order.
        // This preserves the ordering of live epsilon anonymous nonterminals.
        foreach (nonterminal; this.gammaEAG.hyperEBNFGrammar.nonterminals)
            if (nonterminal !in omittedDirectOperatorHelpers)
                findOrCreateHNont(nonterminal);

        // Walk only named rules; anonymous nonterminal rules are embedded in
        // operator nodes and processed recursively by buildHyperFactor.
        foreach (rule; this.gammaEAG.hyperEBNFGrammar.rules)
        {
            if (rule is null) continue;

            Nonterminal nonterminal = rule.lhs.nonterminal;
            const int   gammaSym   = findOrCreateHNont(nonterminal);
            this.ruleByHNontSym[gammaSym] = rule;

            this.hNont[gammaSym].IsToken =
                this.hNont[gammaSym].IsToken ||
                (nonterminal in this.gammaEAG.lexicalHyperNonterminals) !is null;

            if (auto op = rule.directOperator)
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

        if (this.gammaEAG.hyperEBNFGrammar is null)
            return;

        this.affixBuilder.reset;

        // Pass 1: build all DomBuf signatures first.
        // Epsilon sets HNont[Sym].Sig during parsing, before Traverse; we must
        // replicate that so that forward-referenced nonterminals (e.g. A used in
        // S before A is defined) already have their Sig when we build params.
        foreach (gammaSym; EAG.firstHNont .. cast(int) this.hNont.length)
        {
            if (this.hNont[gammaSym].Def is null)
                continue;

            Rule rule = this.ruleByHNontSym.get(gammaSym, null);

            if (rule is null)
                continue;

            this.hNont[gammaSym].Sig = buildAffixSig(gammaSym, rule);
        }

        // Pass 2: build params, scopes and variables — mirrors epsilon's Traverse.
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
                    auto terms = this.gammaEAG.hyperEBNFGrammar.terms(endP.key);
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
                    auto terms = this.gammaEAG.hyperEBNFGrammar.terms(endP.key);
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

                // RepetitionAlternative: pick up trailing actual params (mirrors epsilon's
                // HyperExpr Left=='{' and CheckRep logic).
                //
                // repAlt.params originates from either:
                //   - spareActualParams  (standalone <...> not belonging to any nont) — always
                //     becomes gammaAlt.Actual, mirroring epsilon's direct Actual assignment.
                //   - undecidedActualParams (the <...> after the last named nont in the rhs) —
                //     only becomes gammaAlt.Actual when CheckRep fires, i.e. when that last
                //     nont's Sig is WellMatched with empty (0-arity).
                //
                // Distinguish by checking whether the last rhs node carries the same params key.
                bool repActualIsUndecided = false;

                if (auto repAlt = cast(RepetitionAlternative) alternative)
                {
                    if (repAlt.params !is null)
                    {
                        // Check if repAlt.params belongs to the last rhs nont (undecided).
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
                            // Spare (standalone): always becomes gammaAlt.Actual.
                            auto terms = this.gammaEAG.hyperEBNFGrammar.terms(repAlt.params.key);
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

    // Build DomBuf signature for a HNont; returns the Sig index (into domBuf).
    // Mirrors epsilon's AppDom + SigOK sequence.
    private int buildAffixSig(int gammaSym, Rule rule)
    {
        auto lhsNode = cast(HyperLhsNode) rule.lhs;
        Signature sig = lhsNode !is null ? lhsNode.signature : null;

        if (sig !is null && !sig.isEmpty)
        {
            foreach (i, dir; sig.direction)
            {
                ensureDomBuf;
                const mNontSym = internMNont(sig.domains[i].toString);
                this.domBuf[this.nextDom++] = (dir == Direction.output) ? mNontSym : -mNontSym;
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
            ensureDomBuf;
            this.domBuf[this.nextDom] = EAG.nil;
            ++this.nextDom;
            this.curSig = this.nextDom;
        }
        else
        {
            // Subsequent call: discard tentative entries (reset back to curSig).
            ensureDomBuf;
            this.domBuf[this.nextDom] = EAG.nil;
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

        auto terms = this.gammaEAG.hyperEBNFGrammar.terms(hln.params.key);

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

            ensureParamBuf;
            this.paramBuf[this.nextParam].Affixform = tree;
            this.paramBuf[this.nextParam].Pos       = pos;
            this.paramBuf[this.nextParam].isDef     = isDef;
            ++this.nextParam;
        }
        // Nil terminator
        ensureParamBuf;
        this.paramBuf[this.nextParam].Affixform = EAG.nil;
        this.paramBuf[this.nextParam].Pos       = pos;
        ++this.nextParam;

        return EAG.ParamsDesc(startParam, pos);
    }

    // Determine isDef for the i-th param given the signature and side (Lhs or not).
    // Mirrors: isDef = Lhs && DomBuf[Dom] < 0 || !Lhs && DomBuf[Dom] > 0.
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
    // Returns a non-negative NodeBuf index (Composite) or
    // a negative VarBuf index (Variable — mirrors the negative convention).
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
                // Epsilon stores the lexer token's symbol-table id plus two,
                // rather than the literal integer.  The shared table already
                // contains this token after epsilon's analysis pass.
                num = sign * (cast(int) eag.symbolTable.intern(v.number.get) + 2);
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
        ensureNodeBuf(c.terms.length + 1);
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

                ensureVarBuf;
                this.varBuf[newV].Sym  = sym;
                this.varBuf[newV].Num  = num;
                this.varBuf[newV].Pos  = pos;
                this.varBuf[newV].Def  = isDef;
                this.varBuf[newV].Neg  = v;
                this.varBuf[v].Neg     = newV;
                ++this.nextVarBuf;
                return newV;
            }
        }
        // New variable.
        const int newV = this.nextVarBuf;

        ensureVarBuf;
        this.varBuf[newV].Sym  = sym;
        this.varBuf[newV].Num  = num;
        this.varBuf[newV].Pos  = pos;
        this.varBuf[newV].Def  = isDef;
        this.varBuf[newV].Neg  = EAG.nil;
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
                auto terms = this.gammaEAG.hyperEBNFGrammar.terms(hsn.params.key);

                nont.Actual = buildAffixTermsParamsDesc(terms, refSig, false,
                    hsn.params.position);
            }
        }
        else if (auto op = cast(Operator) node)
        {
            // Actual params placed before the operator bracket (op.params)
            if (op.params !is null)
            {
                auto terms = this.gammaEAG.hyperEBNFGrammar.terms(op.params.key);

                nont.Actual = buildAffixTermsParamsDesc(terms, refSig, false,
                    op.params.position);
            }
        }
    }

    // Dynamic array growth helpers — keep arrays large enough.
    private void ensureDomBuf()
    {
        while (this.nextDom + 1 >= this.domBuf.length)
            this.domBuf.length = this.domBuf.length * 2 + 1;
    }

    private void ensureParamBuf()
    {
        while (this.nextParam + 1 >= this.paramBuf.length)
            this.paramBuf.length = this.paramBuf.length * 2 + 1;
    }

    private void ensureNodeBuf(size_t needed = 1)
    {
        while (this.nextNode + needed >= this.nodeBuf.length)
            this.nodeBuf.length = this.nodeBuf.length * 2 + 1;
    }

    private void ensureVarBuf()
    {
        while (this.nextVarBuf + 1 >= this.varBuf.length)
            this.varBuf.length = this.varBuf.length * 2 + 1;
    }

    private void affixBuildMAltBijection(
        ref int[int] gammaToEpsilonMAlt, const int[int] gammaToEpsilonMNont)
    {
        foreach (gammaSym; EAG.firstMNont .. cast(int) this.mNont.length)
        {
            const epsilonSymP = gammaSym in gammaToEpsilonMNont;

            if (epsilonSymP is null)
                continue;

            int gammaAlt   = this.mNont[gammaSym].MRule;
            int epsilonAlt = eag.MNont[*epsilonSymP].MRule;

            while (gammaAlt != EAG.nil && epsilonAlt != EAG.nil)
            {
                gammaToEpsilonMAlt[gammaAlt] = epsilonAlt;
                gammaAlt   = this.mAlt[gammaAlt].Next;
                epsilonAlt = eag.MAlt[epsilonAlt].Next;
            }
        }
    }

    private void affixCompareScope(string label, EAG.ScopeDesc gammaScope,
                                    EAG.ScopeDesc epsilonScope,
                                    const int[int] gammaToEpsilonMNont,
                                    ref int[int] gammaToEpsilonVar, ref int count)
    {
        const gammaSize   = gammaScope.End - gammaScope.Beg;
        const epsilonSize = epsilonScope.End - epsilonScope.Beg;

        if (gammaSize != epsilonSize)
        {
            error!"compareAffixes: %s scope size gamma=%s EAG=%s"(
                label, gammaSize, epsilonSize);
            ++count;
        }

        const pairLen = gammaSize < epsilonSize ? gammaSize : epsilonSize;

        foreach (offset; 0 .. pairLen)
            gammaToEpsilonVar[gammaScope.Beg + offset] = epsilonScope.Beg + offset;

        foreach (offset; 0 .. pairLen)
        {
            const gammaVarIndex   = gammaScope.Beg + offset;
            const epsilonVarIndex = epsilonScope.Beg + offset;
            const gammaVar        = this.varBuf[gammaVarIndex];
            const epsilonVar      = eag.Var[epsilonVarIndex];
            const translatedSym   = gammaToEpsilonMNont.get(gammaVar.Sym, int.min);

            if (translatedSym != epsilonVar.Sym)
            {
                error!"compareAffixes: %s var[%s] symbol maps to %s, expected %s"(
                    label, offset, translatedSym, epsilonVar.Sym);
                ++count;
            }
            if (gammaVar.Num != epsilonVar.Num)
            {
                error!"compareAffixes: %s var[%s] Num gamma=%s EAG=%s"(
                    label, offset, gammaVar.Num, epsilonVar.Num);
                ++count;
            }
            if (gammaVar.Def != epsilonVar.Def)
            {
                error!"compareAffixes: %s var[%s] Def gamma=%s EAG=%s"(
                    label, offset, gammaVar.Def, epsilonVar.Def);
                ++count;
            }

            const translatedNeg = gammaVar.Neg == EAG.nil
                ? EAG.nil
                : gammaToEpsilonVar.get(gammaVar.Neg, int.min);

            if (translatedNeg != epsilonVar.Neg)
            {
                error!"compareAffixes: %s var[%s] Neg maps to %s, expected %s"(
                    label, offset, translatedNeg, epsilonVar.Neg);
                ++count;
            }
        }
    }

    private void affixCompareTree(string label, int gammaRoot, int epsilonRoot,
                                   const int[int] gammaToEpsilonMNont,
                                   const int[int] gammaToEpsilonMAlt,
                                   const int[int] gammaToEpsilonVar, ref int count)
    {
        const gammaIsVar   = gammaRoot < EAG.nil;
        const epsilonIsVar = epsilonRoot < EAG.nil;

        if (gammaIsVar != epsilonIsVar)
        {
            error!"compareAffixes: %s tree root type gamma=%s EAG=%s"(
                label, gammaIsVar ? "variable" : "composite",
                epsilonIsVar ? "variable" : "composite");
            ++count;
            return;
        }

        if (gammaIsVar)
        {
            const translatedVar = gammaToEpsilonVar.get(-gammaRoot, int.min);

            if (translatedVar != -epsilonRoot)
            {
                error!"compareAffixes: %s variable root maps to %s, expected %s"(
                    label, translatedVar, -epsilonRoot);
                ++count;
            }
            return;
        }

        if (gammaRoot <= EAG.nil || epsilonRoot <= EAG.nil
            || gammaRoot >= cast(int) this.nodeBuf.length
            || epsilonRoot >= cast(int) eag.NodeBuf.length)
        {
            error!"compareAffixes: %s invalid composite root gamma=%s EAG=%s"(
                label, gammaRoot, epsilonRoot);
            ++count;
            return;
        }

        const gammaMAlt   = this.nodeBuf[gammaRoot];
        const epsilonMAlt = eag.NodeBuf[epsilonRoot];
        const translatedMAlt = gammaToEpsilonMAlt.get(gammaMAlt, int.min);

        if (translatedMAlt != epsilonMAlt)
        {
            error!"compareAffixes: %s composite meta alternative maps to %s, expected %s"(
                label, translatedMAlt, epsilonMAlt);
            ++count;
        }

        if (gammaMAlt <= EAG.nil || gammaMAlt >= cast(int) this.mAlt.length
            || epsilonMAlt <= EAG.nil || epsilonMAlt >= eag.NextMAlt)
            return;

        const gammaArity   = this.mAlt[gammaMAlt].Arity;
        const epsilonArity = eag.MAlt[epsilonMAlt].Arity;

        if (gammaArity != epsilonArity)
        {
            error!"compareAffixes: %s composite arity gamma=%s EAG=%s"(
                label, gammaArity, epsilonArity);
            ++count;
        }

        const childCount = gammaArity < epsilonArity ? gammaArity : epsilonArity;

        foreach (child; 0 .. childCount)
            affixCompareTree(format!"%s child[%s]"(label, child),
                this.nodeBuf[gammaRoot + child + 1], eag.NodeBuf[epsilonRoot + child + 1],
                gammaToEpsilonMNont, gammaToEpsilonMAlt, gammaToEpsilonVar, count);
    }

    private void affixCompareParams(string label, EAG.ParamsDesc gammaParams,
                                     EAG.ParamsDesc epsilonParams,
                                     const int[int] gammaToEpsilonMNont,
                                     const int[int] gammaToEpsilonMAlt,
                                     const int[int] gammaToEpsilonVar, ref int count)
    {
        int gammaParam   = gammaParams.Params;
        int epsilonParam = epsilonParams.Params;

        for (int index = 0;; ++index, ++gammaParam, ++epsilonParam)
        {
            const gammaRoot   = this.paramBuf[gammaParam].Affixform;
            const epsilonRoot = eag.ParamBuf[epsilonParam].Affixform;

            if (gammaRoot == EAG.nil && epsilonRoot == EAG.nil)
                return;
            if (gammaRoot == EAG.nil || epsilonRoot == EAG.nil)
            {
                error!"compareAffixes: %s parameter count differs"(label);
                ++count;
                return;
            }

            if (this.paramBuf[gammaParam].isDef != eag.ParamBuf[epsilonParam].isDef)
            {
                error!"compareAffixes: %s param[%s] isDef gamma=%s EAG=%s"(
                    label, index, this.paramBuf[gammaParam].isDef,
                    eag.ParamBuf[epsilonParam].isDef);
                ++count;
            }

            affixCompareTree(format!"%s param[%s]"(label, index), gammaRoot, epsilonRoot,
                gammaToEpsilonMNont, gammaToEpsilonMAlt, gammaToEpsilonVar, count);
        }
    }

    private int compareAffixes()
    {
        int count = 0;

        // ----------------------------------------------------------------
        // We need the HNont bijection from compareHyper; rebuild it here.
        // ----------------------------------------------------------------
        int[int] gammaToEpsilonHNont;

        foreach (gammaSym; EAG.firstHNont .. cast(int) this.hNont.length)
        {
            if (this.hNont[gammaSym].anonymous)
                continue;

            const id = this.hNont[gammaSym].Id;
            int   epsilonSym = EAG.firstHNont;

            while (epsilonSym < eag.NextHNont && eag.HNont[epsilonSym].Id != id)
                ++epsilonSym;

            if (epsilonSym < eag.NextHNont)
                gammaToEpsilonHNont[gammaSym] = epsilonSym;
        }

        int[] epsilonAnonymList;

        foreach (sym; EAG.firstHNont .. eag.NextHNont)
            if (eag.HNont[sym].Id < 0 && eag.HNont[sym].Def !is null)
                epsilonAnonymList ~= sym;

        const pairLen = this.hAnonymNonts.length < epsilonAnonymList.length
            ? this.hAnonymNonts.length : epsilonAnonymList.length;

        foreach (k; 0 .. pairLen)
            gammaToEpsilonHNont[this.hAnonymNonts[k]] = epsilonAnonymList[k];

        // MNont bijection (by symbolTable Id)
        int[int] gammaToEpsilonMNont;

        foreach (gammaSym; EAG.firstMNont .. cast(int) this.mNont.length)
        {
            const id = this.mNont[gammaSym].Id;
            int   esym = EAG.firstMNont;

            while (esym < eag.NextMNont && eag.MNont[esym].Id != id)
                ++esym;

            if (esym < eag.NextMNont)
                gammaToEpsilonMNont[gammaSym] = esym;
        }

        int[int] gammaToEpsilonMAlt;

        affixBuildMAltBijection(gammaToEpsilonMAlt, gammaToEpsilonMNont);

        // Variables are scoped per alternative (and per Rep/Opt formal list),
        // so their ordinal position within a corresponding scope provides the
        // stable bijection used by parameter tree roots and Neg links.
        int[int] gammaToEpsilonVar;

        // ----------------------------------------------------------------
        // Compare DomBuf signatures per HNont.
        // ----------------------------------------------------------------
        foreach (gammaSym; EAG.firstHNont .. cast(int) this.hNont.length)
        {
            if (this.hNont[gammaSym].Def is null)
                continue;

            const eSymP = gammaSym in gammaToEpsilonHNont;

            if (eSymP is null)
                continue;

            const eSym    = *eSymP;
            const symName = this.hNont[gammaSym].anonymous
                ? format!"A%s"(-this.hNont[gammaSym].Id)
                : eag.symbolTable.symbol(this.hNont[gammaSym].Id);

            const gSig = this.hNont[gammaSym].Sig;
            const eSig = eag.HNont[eSym].Sig;

            // Compare the domain sequences symbolically.
            int gd = (gSig >= 0) ? gSig : 0;
            int ed = (eSig >= 0) ? eSig : 0;

            for (;;)
            {
                const gDom = (gd < cast(int) this.domBuf.length) ? this.domBuf[gd] : EAG.nil;
                const eDom = (ed < cast(int) eag.DomBuf.length)  ? eag.DomBuf[ed]  : EAG.nil;

                if (gDom == EAG.nil && eDom == EAG.nil)
                    break;

                if (gDom == EAG.nil || eDom == EAG.nil)
                {
                    error!"compareAffixes: HNont '%s' signature length differs"(symName);
                    ++count;
                    break;
                }

                // Translate the sign separately.
                const gDir    = gDom < 0 ? -1 : 1;
                const eDir    = eDom < 0 ? -1 : 1;

                if (gDir != eDir)
                {
                    error!"compareAffixes: HNont '%s' signature direction differs at domain pos"(symName);
                    ++count;
                }
                else
                {
                    const gMNont = gDir > 0 ? gDom : -gDom;
                    const eMNont = eDir > 0 ? eDom : -eDom;
                    const translated = gammaToEpsilonMNont.get(gMNont, int.min);

                    if (translated != eMNont)
                    {
                        error!"compareAffixes: HNont '%s' signature domain '%s' maps to %s, expected %s"(
                            symName,
                            eag.symbolTable.symbol(this.mNont[gMNont].Id),
                            translated, eMNont);
                        ++count;
                    }
                }
                ++gd;
                ++ed;
            }
        }

        // ----------------------------------------------------------------
        // Compare per-Alt Formal/Actual descriptors, scoped variables, and
        // actual descriptors on every nonterminal factor.
        // ----------------------------------------------------------------
        foreach (gammaSym; EAG.firstHNont .. cast(int) this.hNont.length)
        {
            if (this.hNont[gammaSym].Def is null)
                continue;

            const eSymP = gammaSym in gammaToEpsilonHNont;

            if (eSymP is null)
                continue;

            const eSym    = *eSymP;
            const symName = this.hNont[gammaSym].anonymous
                ? format!"A%s"(-this.hNont[gammaSym].Id)
                : eag.symbolTable.symbol(this.hNont[gammaSym].Id);

            EAG.Alt gammaAlt   = this.hNont[gammaSym].Def.Sub;
            EAG.Alt epsilonAlt = eag.HNont[eSym].Def.Sub;

            for (int ai = 0; gammaAlt !is null && epsilonAlt !is null; ++ai)
            {
                const label = format!"HNont '%s' alt[%s]"(symName, ai);

                affixCompareScope(label, gammaAlt.Scope, epsilonAlt.Scope,
                    gammaToEpsilonMNont, gammaToEpsilonVar, count);
                affixCompareParams(format!"%s Formal"(label), gammaAlt.Formal,
                    epsilonAlt.Formal, gammaToEpsilonMNont, gammaToEpsilonMAlt,
                    gammaToEpsilonVar, count);
                affixCompareParams(format!"%s Actual"(label), gammaAlt.Actual,
                    epsilonAlt.Actual, gammaToEpsilonMNont, gammaToEpsilonMAlt,
                    gammaToEpsilonVar, count);

                EAG.Factor gammaFactor   = gammaAlt.Sub;
                EAG.Factor epsilonFactor = epsilonAlt.Sub;

                for (int fi = 0; gammaFactor !is null && epsilonFactor !is null; ++fi)
                {
                    auto gammaNont   = cast(EAG.Nont) gammaFactor;
                    auto epsilonNont = cast(EAG.Nont) epsilonFactor;

                    if (gammaNont !is null && epsilonNont !is null)
                        affixCompareParams(format!"%s factor[%s] Actual"(label, fi),
                            gammaNont.Actual, epsilonNont.Actual,
                            gammaToEpsilonMNont, gammaToEpsilonMAlt,
                            gammaToEpsilonVar, count);

                    gammaFactor   = gammaFactor.Next;
                    epsilonFactor = epsilonFactor.Next;
                }

                gammaAlt   = gammaAlt.Next;
                epsilonAlt = epsilonAlt.Next;
            }
        }

        // ----------------------------------------------------------------
        // Compare Rep/Opt Formal param counts and scope sizes.
        // ----------------------------------------------------------------
        foreach (gammaSym; EAG.firstHNont .. cast(int) this.hNont.length)
        {
            const eSymP = gammaSym in gammaToEpsilonHNont;

            if (eSymP is null)
                continue;

            const eSym    = *eSymP;
            const symName = this.hNont[gammaSym].anonymous
                ? format!"A%s"(-this.hNont[gammaSym].Id)
                : eag.symbolTable.symbol(this.hNont[gammaSym].Id);

            if (auto rep = cast(EAG.Rep) this.hNont[gammaSym].Def)
            {
                if (auto eRep = cast(EAG.Rep) eag.HNont[eSym].Def)
                {
                    const label = format!"HNont '%s' Rep"(symName);

                    affixCompareScope(label, rep.Scope, eRep.Scope,
                        gammaToEpsilonMNont, gammaToEpsilonVar, count);
                    affixCompareParams(format!"%s Formal"(label), rep.Formal,
                        eRep.Formal, gammaToEpsilonMNont, gammaToEpsilonMAlt,
                        gammaToEpsilonVar, count);
                }
            }
            else if (auto opt = cast(EAG.Opt) this.hNont[gammaSym].Def)
            {
                if (auto eOpt = cast(EAG.Opt) eag.HNont[eSym].Def)
                {
                    const label = format!"HNont '%s' Opt"(symName);

                    affixCompareScope(label, opt.Scope, eOpt.Scope,
                        gammaToEpsilonMNont, gammaToEpsilonVar, count);
                    affixCompareParams(format!"%s Formal"(label), opt.Formal,
                        eOpt.Formal, gammaToEpsilonMNont, gammaToEpsilonMAlt,
                        gammaToEpsilonVar, count);
                }
            }
        }

        // ----------------------------------------------------------------
        // Compare total Var counts.
        // ----------------------------------------------------------------
        const gVarCount = this.nextVarBuf - EAG.firstVar;
        const eVarCount = eag.NextVar      - EAG.firstVar;

        if (gVarCount != eVarCount)
        {
            error!"compareAffixes: total Var count gamma=%s EAG=%s"(gVarCount, eVarCount);
            ++count;
        }

        if (count == 0)
            trace!"compareAffixes: OK";
        return count;
    }

    // =========================================================================
    // EAG sets
    // =========================================================================

    private void buildSets()
    {
        if (this.gammaEAG.plainHyperGrammar is null)
            return;

        auto grammar = this.gammaEAG.plainHyperGrammar;
        auto lexicalNonterminals = this.gammaEAG.lexicalHyperNonterminals;
        auto properties = new GrammarProperties(grammar, lexicalNonterminals);

        this.reachableHNonterminals.length = this.hNont.length;
        this.productiveHNonterminals.length = this.hNont.length;
        this.nullableHNonterminals.length = this.hNont.length;

        foreach (nonterminal; this.gammaEAG.plainHyperGrammar.nonterminals)
        {
            const gammaSym = this.hNontByNonterminal.get(nonterminal, int.min);

            if (gammaSym == int.min || this.hNont[gammaSym].Def is null)
                continue;

            this.reachableHNonterminals[gammaSym] = properties.isReachable(nonterminal);
            this.productiveHNonterminals[gammaSym] = properties.isProductive(nonterminal);
            this.nullableHNonterminals[gammaSym] = properties.isNullable(nonterminal);
        }
    }

    private int compareSets()
    {
        int count = 0;
        int[int] gammaToEpsilonHNont;

        foreach (gammaSym; EAG.firstHNont .. cast(int) this.hNont.length)
        {
            if (this.hNont[gammaSym].anonymous)
                continue;

            const id = this.hNont[gammaSym].Id;
            int epsilonSym = EAG.firstHNont;

            while (epsilonSym < eag.NextHNont && eag.HNont[epsilonSym].Id != id)
                ++epsilonSym;

            if (epsilonSym < eag.NextHNont)
                gammaToEpsilonHNont[gammaSym] = epsilonSym;
        }

        int[] epsilonAnonymous;

        foreach (epsilonSym; EAG.firstHNont .. eag.NextHNont)
            if (eag.HNont[epsilonSym].Id < 0 && eag.HNont[epsilonSym].Def !is null)
                epsilonAnonymous ~= epsilonSym;

        const anonymousCount = this.hAnonymNonts.length < epsilonAnonymous.length
            ? this.hAnonymNonts.length : epsilonAnonymous.length;

        foreach (index; 0 .. anonymousCount)
            gammaToEpsilonHNont[this.hAnonymNonts[index]] = epsilonAnonymous[index];

        foreach (gammaSym; EAG.firstHNont .. cast(int) this.hNont.length)
        {
            const epsilonSymP = gammaSym in gammaToEpsilonHNont;

            if (epsilonSymP is null || this.hNont[gammaSym].Def is null)
                continue;

            const epsilonSym = *epsilonSymP;
            const symbolName = this.hNont[gammaSym].anonymous
                ? format!"A%s"(-this.hNont[gammaSym].Id)
                : eag.symbolTable.symbol(this.hNont[gammaSym].Id);

            count += compareSet("Reach", symbolName, this.reachableHNonterminals[gammaSym], eag.Reach[epsilonSym]);
            count += compareSet("Prod", symbolName, this.productiveHNonterminals[gammaSym], eag.Prod[epsilonSym]);
            count += compareSet("Null", symbolName, this.nullableHNonterminals[gammaSym], eag.Null[epsilonSym]);
        }

        if (count == 0)
            trace!"compareSets: OK";
        return count;
    }

    private static int compareSet(string setName, string symbolName, bool gammaValue, bool epsilonValue)
    {
        if (gammaValue == epsilonValue)
            return 0;

        error!"compareSets: %s['%s'] gamma=%s EAG=%s"(setName, symbolName, gammaValue, epsilonValue);
        return 1;
    }

    private int compareHyper()
    {
        int count = 0;

        // ----------------------------------------------------------------
        // Build a bijection: gamma HNont index → epsilon HNont index.
        //   Named:     match by symbolTable Id.
        //   Anonymous: match by encounter order (both created left-to-right).
        // ----------------------------------------------------------------
        int[int] gammaToEpsilonHNont; // gamma index → epsilon index

        // Exclude anonymous nonterminals removed by epsilon's Shrink().
        int[] epsilonAnonymList;
        int   epsilonShrunkAnonymCount = 0;

        foreach (sym; EAG.firstHNont .. eag.NextHNont)
            if (eag.HNont[sym].Id < 0)
            {
                if (eag.HNont[sym].Def !is null)
                    epsilonAnonymList ~= sym;
                else
                    ++epsilonShrunkAnonymCount;
            }

        // Map named nonterminals.
        foreach (gammaSym; EAG.firstHNont .. cast(int) this.hNont.length)
        {
            if (this.hNont[gammaSym].anonymous)
                continue;

            const id = this.hNont[gammaSym].Id;
            int   epsilonSym = EAG.firstHNont;

            while (epsilonSym < eag.NextHNont && eag.HNont[epsilonSym].Id != id)
                ++epsilonSym;

            if (epsilonSym >= eag.NextHNont)
            {
                error!"compareHyper: named HNont '%s' not found in EAG"(
                    eag.symbolTable.symbol(id));
                ++count;
            }
            else
            {
                gammaToEpsilonHNont[gammaSym] = epsilonSym;
            }
        }

        // Map anonymous nonterminals by encounter order.
        if (this.hAnonymNonts.length != epsilonAnonymList.length)
        {
            error!"compareHyper: anonymous HNont count gamma=%s vs EAG=%s"(
                this.hAnonymNonts.length, epsilonAnonymList.length);
            ++count;
        }

        const pairLen = this.hAnonymNonts.length < epsilonAnonymList.length
            ? this.hAnonymNonts.length : epsilonAnonymList.length;

        foreach (k; 0 .. pairLen)
            gammaToEpsilonHNont[this.hAnonymNonts[k]] = epsilonAnonymList[k];

        // Ignore anonymous nonterminals removed by epsilon's Shrink().
        if (cast(int) this.hNont.length + epsilonShrunkAnonymCount != eag.NextHNont)
        {
            error!"compareHyper: gamma has %s HNont entries but EAG (excluding shrunk) has %s"(
                this.hNont.length, eag.NextHNont - epsilonShrunkAnonymCount);
            ++count;
        }

        // ----------------------------------------------------------------
        // Build forward bijection for HTerm.
        // ----------------------------------------------------------------
        int[int] gammaToHTerm; // gamma HTerm index → epsilon HTerm index

        foreach (gammaSym; EAG.firstHTerm .. cast(int) this.hTerm.length)
        {
            const id = this.hTerm[gammaSym].Id;
            int   epsilonSym = EAG.firstHTerm;

            while (epsilonSym < eag.NextHTerm && eag.HTerm[epsilonSym].Id != id)
                ++epsilonSym;

            if (epsilonSym >= eag.NextHTerm)
            {
                error!"compareHyper: HTerm '%s' not found in EAG"(
                    eag.symbolTable.symbol(id));
                ++count;
            }
            else
            {
                gammaToHTerm[gammaSym] = epsilonSym;
            }
        }

        if (cast(int) this.hTerm.length != eag.NextHTerm)
        {
            error!"compareHyper: gamma has %s HTerm entries but EAG has %s"(
                this.hTerm.length, eag.NextHTerm);
            ++count;
        }

        // ----------------------------------------------------------------
        // Compare each HNont entry that has a Def.
        // ----------------------------------------------------------------
        foreach (gammaSym; EAG.firstHNont .. cast(int) this.hNont.length)
        {
            const epsilonSymP = gammaSym in gammaToEpsilonHNont;

            if (epsilonSymP is null)
                continue; // already reported (bijection gap)

            const epsilonSym = *epsilonSymP;

            // Convenient name for messages.
            const symName = this.hNont[gammaSym].anonymous
                ? format!"A%s"(-this.hNont[gammaSym].Id)
                : eag.symbolTable.symbol(this.hNont[gammaSym].Id);

            // ---- IsToken ----
            if (this.hNont[gammaSym].IsToken != eag.HNont[epsilonSym].IsToken)
            {
                error!"compareHyper: HNont '%s' IsToken %s != %s"(
                    symName,
                    this.hNont[gammaSym].IsToken, eag.HNont[epsilonSym].IsToken);
                ++count;
            }

            // ---- Def type ----
            const gammaHasDef   = this.hNont[gammaSym].Def !is null;
            const epsilonHasDef = eag.HNont[epsilonSym].Def !is null;

            if (gammaHasDef != epsilonHasDef)
            {
                error!"compareHyper: HNont '%s' Def presence gamma=%s EAG=%s"(
                    symName, gammaHasDef, epsilonHasDef);
                ++count;
                continue;
            }
            if (!gammaHasDef)
                continue; // both null — after Shrink, valid to match

            const gammaIsGrp = cast(EAG.Grp) this.hNont[gammaSym].Def !is null;
            const gammaIsRep = cast(EAG.Rep) this.hNont[gammaSym].Def !is null;
            const gammaIsOpt = cast(EAG.Opt) this.hNont[gammaSym].Def !is null;
            const epsIsGrp   = cast(EAG.Grp) eag.HNont[epsilonSym].Def !is null;
            const epsIsRep   = cast(EAG.Rep) eag.HNont[epsilonSym].Def !is null;
            const epsIsOpt   = cast(EAG.Opt) eag.HNont[epsilonSym].Def !is null;

            if (gammaIsGrp != epsIsGrp || gammaIsRep != epsIsRep || gammaIsOpt != epsIsOpt)
            {
                const gammaDefType = gammaIsGrp ? "Grp" : gammaIsRep ? "Rep" : "Opt";
                const epsDefType   = epsIsGrp   ? "Grp" : epsIsRep   ? "Rep" : "Opt";

                error!"compareHyper: HNont '%s' Def type gamma=%s EAG=%s"(
                    symName, gammaDefType, epsDefType);
                ++count;
                // still walk the alt chains
            }

            // ---- Alt chains ----
            EAG.Alt gammaAlt   = this.hNont[gammaSym].Def.Sub;
            EAG.Alt epsilonAlt = eag.HNont[epsilonSym].Def.Sub;

            for (int altIndex = 0; gammaAlt !is null || epsilonAlt !is null; ++altIndex)
            {
                if (gammaAlt is null || epsilonAlt is null)
                {
                    error!"compareHyper: HNont '%s' alternative count differs"(symName);
                    ++count;
                    break;
                }

                // ---- Factor chains ----
                EAG.Factor gammaF   = gammaAlt.Sub;
                EAG.Factor epsilonF = epsilonAlt.Sub;

                for (int factorIndex = 0; gammaF !is null || epsilonF !is null; ++factorIndex)
                {
                    if (gammaF is null || epsilonF is null)
                    {
                        error!"compareHyper: HNont '%s' alt[%s] factor count differs"(
                            symName, altIndex);
                        ++count;
                        break;
                    }

                    const gammaIsTerm   = cast(EAG.Term) gammaF !is null;
                    const epsilonIsTerm = cast(EAG.Term) epsilonF !is null;

                    if (gammaIsTerm != epsilonIsTerm)
                    {
                        error!"compareHyper: HNont '%s' alt[%s] factor[%s] type mismatch"(
                            symName, altIndex, factorIndex);
                        ++count;
                    }
                    else if (gammaIsTerm)
                    {
                        // Both Term: compare symbol
                        const gammaTermSym   = (cast(EAG.Term) gammaF).Sym;
                        const epsilonTermSym = (cast(EAG.Term) epsilonF).Sym;
                        const translated     = gammaToHTerm.get(gammaTermSym, int.min);

                        if (translated != epsilonTermSym)
                        {
                            const gammaName = eag.symbolTable.symbol(this.hTerm[gammaTermSym].Id);

                            error!"compareHyper: HNont '%s' alt[%s] factor[%s] Term '%s' maps to %s, expected %s"(
                                symName, altIndex, factorIndex,
                                gammaName, translated, epsilonTermSym);
                            ++count;
                        }
                    }
                    else
                    {
                        // Both Nont: compare symbol
                        const gammaNontSym   = (cast(EAG.Nont) gammaF).Sym;
                        const epsilonNontSym = (cast(EAG.Nont) epsilonF).Sym;
                        const translated     = gammaToEpsilonHNont.get(gammaNontSym, int.min);

                        if (translated != epsilonNontSym)
                        {
                            const gammaName = this.hNont[gammaNontSym].anonymous
                                ? format!"A%s"(-this.hNont[gammaNontSym].Id)
                                : eag.symbolTable.symbol(this.hNont[gammaNontSym].Id);

                            error!"compareHyper: HNont '%s' alt[%s] factor[%s] Nont '%s' maps to %s, expected %s"(
                                symName, altIndex, factorIndex,
                                gammaName, translated, epsilonNontSym);
                            ++count;
                        }
                    }

                    gammaF   = gammaF.Next;
                    epsilonF = epsilonF.Next;
                }

                gammaAlt   = gammaAlt.Next;
                epsilonAlt = epsilonAlt.Next;
            }
        }

        if (count == 0)
            trace!"compareHyper: OK";
        return count;
    }

    // =========================================================================
    // Private helpers
    // =========================================================================

    private int internMNont(string name) @safe
    {
        const id = cast(int) eag.symbolTable.intern(name);

        if (auto p = id in this.mNontById)
            return *p;

        const sym = cast(int) this.mNont.length;

        this.mNont ~= EAG.MNontRecord(id, EAG.nil, EAG.nil, false);
        this.mNontById[id] = sym;
        return sym;
    }

    private int internMTerm(string name) @safe
    {
        const id = cast(int) eag.symbolTable.intern(name);

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
        // epsilon's MetaExpr does AppMemb(NewMAlt(...)) — the alt's own index
        // is appended into MembBuf immediately after the nil sentinel.
        this.membBuf ~= index;
    }

    // -------------------------------------------------------------------------
    // Hyper grammar helpers
    // -------------------------------------------------------------------------

    /**
     * Find (or create) the builder's HNont entry for the given gamma nonterminal.
     * Named nonterminals are keyed by their symbolTable Id.
     * Anonymous nonterminals use a negative Id counter (matching epsilon's NextAnonym).
     */
    private int findOrCreateHNont(Nonterminal nonterminal)
    {
        if (auto p = nonterminal in this.hNontByNonterminal)
            return *p;

        const sym = cast(int) this.hNont.length;

        this.hNontByNonterminal[nonterminal] = sym;

        if (cast(AnonymousNonterminal) nonterminal)
        {
            // Anonymous: assign a negative Id matching epsilon's NextAnonym scheme.
            const id = this.hNextAnonym--;

            this.hNont ~= EAG.HNontRecord(id, EAG.nil, -1, null, false);
            this.hAnonymNonts ~= sym;
        }
        else
        {
            // Named: use the shared symbolTable Id.
            const id = cast(int) eag.symbolTable.intern(nonterminal.toString);

            this.hNont ~= EAG.HNontRecord(id, id, -1, null, false);
            this.hNontById[id] = sym;
        }
        return sym;
    }

    /**
     * Find (or create) the builder's HTerm entry for the given terminal name.
     */
    private int findOrCreateHTerm(string name)
    {
        const id = cast(int) eag.symbolTable.intern(name);

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

/**
 * Owns the mutable EAG-affix mirror buffers.  EAGBuilder supplies the grammar
 * projection; this component owns the independently resettable affix state.
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
        this.domBuf = new int[256];
        this.domBuf[0] = EAG.nil;
        this.nextDom = 1;
        this.curSig = 1;
        this.paramBuf = new EAG.ParamRecord[1024];
        this.paramBuf[0].Affixform = EAG.nil;
        this.nextParam = 1;
        this.nodeBuf = new int[1024];
        this.nextNode = EAG.firstNode;
        this.varBuf = new EAG.VarRecord[512];
        this.nextVarBuf = EAG.firstVar;
        this.currentScope = EAG.firstVar;
    }
}

// A named rule that consists solely of an unparameterized EBNF operator has
// the same legacy EAG representation as the operator's generated helper rule.
// The Gamma model deliberately keeps both rules; only this backend elides the
// helper while producing EAG.
private Operator directOperator(Rule rule)
{
    if (cast(AnonymousNonterminal) rule.lhs.nonterminal)
        return null;

    if (rule.alternatives.length != 1)
        return null;

    auto alternative = rule.alternatives.front;
    auto lhs = cast(HyperLhsNode) alternative.lhs;

    if (lhs is null || lhs.params !is null || alternative.rhs.length != 1)
        return null;

    auto op = cast(Operator) alternative.rhs.front;

    if (op is null || op.params !is null)
        return null;
    if (!cast(AnonymousNonterminal) op.rule.lhs.nonterminal)
        return null;

    return op;
}

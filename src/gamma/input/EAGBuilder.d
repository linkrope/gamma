module gamma.input.EAGBuilder;

import EAG = epsilon.eag;
import gamma.grammar.Alternative;
import gamma.grammar.hyper.AnonymousNonterminal;
import gamma.grammar.hyper.HyperLhsNode;
import gamma.grammar.LhsNode;
import gamma.grammar.Node;
import gamma.grammar.Nonterminal;
import gamma.grammar.Rule;
import gamma.grammar.SymbolNode;
import gamma.grammar.Terminal;
import gamma.input.epsilang.analyzer : GammaEAG = EAG;
import io : Position;
import log;
import std.format : format;

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
    private GammaEAG eag;

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
    private int[int] mNontById; // EAG.symbolTable Id -> mNont index
    private int[int] mTermById; // EAG.symbolTable Id -> mTerm index

    // -------------------------------------------------------------------------
    // Hyper grammar mirrors — firstHNont = 0, firstHTerm = 0 (no dummy slot 0)
    // -------------------------------------------------------------------------

    private EAG.HNontRecord[] hNont;          // hNont[i] mirrors EAG.HNont[i]
    private EAG.HTermRecord[] hTerm;          // hTerm[i] mirrors EAG.HTerm[i]

    // Named: symbolTable Id -> hNont index.  Anonymous: not tracked here.
    private int[int]         hNontById;
    // Every nonterminal object -> its hNont index (covers named and anonymous).
    private int[Nonterminal] hNontByNonterminal;
    // Parallel to hNont: the original gamma Nonterminal (for Shrink look-up).
    private Nonterminal[]    hNontNonterminal;
    // HTerm: symbolTable Id -> hTerm index.
    private int[int]         hTermById;

    // Anonymous counter: starts at -1 and decrements, matching epsilon's NextAnonym.
    private int hNextAnonym = -1;

    // Anonymous hNont indices in encounter order (for compareHyper bijection).
    private int[] hAnonymNonts;

    // Counters matching epsilon's NextHAlt / NextHFactor.
    private int nextHAlt    = EAG.firstHAlt;
    private int nextHFactor = EAG.firstHFactor;

    public this(GammaEAG eag)
    {
        this.eag = eag;

        // Reserve slot 0 in each array so real entries start at index 1
        this.mNont   = new EAG.MNontRecord[1];
        this.mTerm   = new EAG.MTermRecord[1];
        this.mAlt    = new EAG.MAltRecord[1];
        this.membBuf = new int[1];

        buildMeta;
        buildHyper;
    }

    /**
     * Diff the builder's internal meta-grammar mirrors against the live EAG globals
     * (already populated by epsilon.analyzer.Analyse()) and log per-field mismatches.
     *
     * Returns: number of differences found (0 = perfect match)
     */
    public int compare()
    {
        return compareMeta + compareHyper;
    }

    // =========================================================================
    // Meta rules
    // =========================================================================

    private void buildMeta()
    {
        foreach (rule; this.eag.metaGrammar.rules)
        {
            Nonterminal nonterminal = (cast(LhsNode) rule.lhs).nonterminal;
            const lhsSym = internMNont(nonterminal.toString);

            this.mNont[lhsSym].IsToken = this.mNont[lhsSym].IsToken || nonterminal in this.eag.lexicalMetaNonterminals;

            foreach (alternative; rule.alternatives)
            {
                const rhs = cast(int) this.membBuf.length;

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
        // EAG.symbolTable is shared with gamma: intern() returns the same Id
        // for the same string regardless of call order, so Ids are stable across
        // both traversals and serve as a reliable join key.
        int[int] mNontByIdMap;

        foreach (sym; EAG.firstMNont .. EAG.NextMNont)
            mNontByIdMap[EAG.MNont[sym].Id] = sym;

        int[int] mTermByIdMap;

        foreach (sym; EAG.firstMTerm .. EAG.NextMTerm)
            mTermByIdMap[EAG.MTerm[sym].Id] = sym;

        // Bijection maps: gamma index → epsilon index
        int[int] gammaToMNont;

        foreach (gammaSym; EAG.firstMNont .. cast(int) this.mNont.length)
        {
            if (auto p = this.mNont[gammaSym].Id in mNontByIdMap)
                gammaToMNont[gammaSym] = *p;
            else
            {
                error!"compareMeta: MNont '%s' not found in EAG"(
                    EAG.symbolTable.symbol(this.mNont[gammaSym].Id));
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
                    EAG.symbolTable.symbol(this.mTerm[gammaSym].Id));
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
            const symName = EAG.symbolTable.symbol(this.mNont[gammaSym].Id);

            if (this.mNont[gammaSym].IsToken != EAG.MNont[sym].IsToken)
            {
                error!"compareMeta: MNont '%s' IsToken %s != %s"(
                    symName,
                    this.mNont[gammaSym].IsToken, EAG.MNont[sym].IsToken);
                ++count;
            }

            int gammaAlt = this.mNont[gammaSym].MRule;
            int alt      = EAG.MNont[sym].MRule;

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
                int i      = EAG.MAlt[alt].Right;

                while (this.membBuf[gammaI] != EAG.nil || EAG.MembBuf[i] != EAG.nil)
                {
                    if (this.membBuf[gammaI] == EAG.nil || EAG.MembBuf[i] == EAG.nil)
                    {
                        error!"compareMeta: MNont '%s' alternative member count differs"(symName);
                        ++count;
                        break;
                    }

                    const gammaVal = this.membBuf[gammaI];
                    const val      = EAG.MembBuf[i];

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
                            ? EAG.symbolTable.symbol(this.mNont[gammaVal].Id)
                            : EAG.symbolTable.symbol(this.mTerm[-gammaVal].Id);

                        error!"compareMeta: MNont '%s' alt member: gamma '%s' maps to %s, expected %s"(
                            symName, gammaName, translated, val);
                        ++count;
                    }

                    ++gammaI;
                    ++i;
                }

                gammaAlt = this.mAlt[gammaAlt].Next;
                alt      = EAG.MAlt[alt].Next;
            }
        }

        // EAG.NextMNont may be larger (epsilon creates extra MNont entries for
        // domain references in hyper rules); only report if the builder has more.
        if (cast(int) this.mNont.length > EAG.NextMNont)
        {
            error!"compareMeta: builder has %s MNont entries but EAG only has %s"(
                this.mNont.length - EAG.firstMNont, EAG.NextMNont - EAG.firstMNont);
            ++count;
        }

        if (cast(int) this.mTerm.length != EAG.NextMTerm)
        {
            error!"compareMeta: builder has %s MTerm entries but EAG has %s"(
                this.mTerm.length - EAG.firstMTerm, EAG.NextMTerm - EAG.firstMTerm);
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
        if (this.eag.hyperEBNFGrammar is null)
            return;

        // Pre-populate hNont for ALL nonterminals in Grammar.nonterminals()
        // index order.  This ensures hAnonymNonts is built in parse-encounter
        // order, which matches epsilon's NewAnonymNont call order.
        foreach (nonterminal; this.eag.hyperEBNFGrammar.nonterminals)
            findOrCreateHNont(nonterminal);

        // Walk only named rules; anonymous nonterminal rules are embedded in
        // operator nodes and processed recursively by buildHyperFactor.
        foreach (rule; this.eag.hyperEBNFGrammar.rules)
        {
            Nonterminal nonterminal = rule.lhs.nonterminal;
            const int   gammaSym   = findOrCreateHNont(nonterminal);

            this.hNont[gammaSym].IsToken =
                this.hNont[gammaSym].IsToken ||
                (nonterminal in this.eag.lexicalHyperNonterminals) !is null;

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

        // ----------------------------------------------------------------
        // Shrink: replicate epsilon's Shrink() post-pass.
        // A named Grp whose single no-formal-params alt references a single
        // anonymous nonterminal with no actual params has its Def replaced by
        // the anonymous nonterminal's Def directly (as epsilon does).
        // ----------------------------------------------------------------
        foreach (gammaSym; EAG.firstHNont .. cast(int) this.hNont.length)
        {
            if (this.hNont[gammaSym].anonymous)
                continue;
            if (this.hNont[gammaSym].Def is null)
                continue;

            auto grp = cast(EAG.Grp) this.hNont[gammaSym].Def;

            if (grp is null)
                continue;

            EAG.Alt a = grp.Sub;

            if (a is null || a.Next !is null)
                continue;

            // Check whether the LHS had formal params (if so, Shrink does not apply).
            auto gammaRule = this.eag.plainHyperGrammar.ruleOf(this.hNontNonterminal[gammaSym]);
            auto lhsNode   = cast(HyperLhsNode) gammaRule.lhs;
            const hasFormals = lhsNode !is null && lhsNode.params !is null;

            if (hasFormals)
                continue;

            if (a.Sub is null)
                continue;

            auto f = cast(EAG.Nont) a.Sub;

            if (f is null || f.Next !is null)
                continue;

            if (!this.hNont[f.Sym].anonymous)
                continue;

            if (f.Actual.Params != EAG.empty)
                continue;

            // Apply Shrink: move anon's Def up to the named HNont.
            this.hNont[gammaSym].Def = this.hNont[f.Sym].Def;
            this.hNont[gammaSym].Sig = this.hNont[f.Sym].Sig;
            this.hNont[f.Sym].Def   = null;

            // Re-link all alts' Up pointer to the named HNont.
            for (EAG.Alt alt = this.hNont[gammaSym].Def.Sub; alt !is null; alt = alt.Next)
                alt.Up = gammaSym;
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
            appendHNont(firstFactor, lastFactor, buildHyperGrpRule(grp.rule), grp.position);
        else if (auto opt = cast(HyperOption) node)
            appendHNont(firstFactor, lastFactor, buildHyperOptRule(opt.rule, opt.position), opt.position);
        else if (auto rep = cast(HyperRepetition) node)
            appendHNont(firstFactor, lastFactor, buildHyperRepRule(rep.rule, rep.position), rep.position);
        else if (auto sn = cast(SymbolNode) node)
        {
            if (cast(Terminal) sn.symbol)
                appendHTerm(firstFactor, lastFactor,
                    findOrCreateHTerm(sn.symbol.toString), sn.position);
            else
                appendHNont(firstFactor, lastFactor,
                    findOrCreateHNont(cast(Nonterminal) sn.symbol), sn.position);
        }
    }

    private int buildHyperGrpRule(Rule rule)
    {
        const int anonSym = findOrCreateHNont(rule.lhs.nonterminal);
        EAG.Alt firstAlt = null;
        EAG.Alt lastAlt  = null;

        foreach (alternative; rule.alternatives)
            buildHyperAlt(anonSym, alternative, firstAlt, lastAlt);

        auto grp = new EAG.Grp;

        grp.Sub = firstAlt;
        this.hNont[anonSym].Def = grp;
        return anonSym;
    }

    private int buildHyperOptRule(Rule rule, Position position)
    {
        const int anonSym = findOrCreateHNont(rule.lhs.nonterminal);
        EAG.Alt firstAlt = null;
        EAG.Alt lastAlt  = null;

        foreach (alternative; rule.alternatives)
            buildHyperAlt(anonSym, alternative, firstAlt, lastAlt);

        auto opt = new EAG.Opt;

        opt.Sub         = firstAlt;
        opt.EmptyAltPos = position;
        opt.Scope.Beg   = EAG.nil;
        opt.Scope.End   = EAG.nil;
        opt.Formal      = EAG.ParamsDesc.init;
        this.hNont[anonSym].Def = opt;
        return anonSym;
    }

    private int buildHyperRepRule(Rule rule, Position position)
    {
        const int anonSym = findOrCreateHNont(rule.lhs.nonterminal);
        EAG.Alt firstAlt = null;
        EAG.Alt lastAlt  = null;

        foreach (alternative; rule.alternatives)
            buildHyperAlt(anonSym, alternative, firstAlt, lastAlt);

        auto rep = new EAG.Rep;

        rep.Sub         = firstAlt;
        rep.EmptyAltPos = position;
        rep.Scope.Beg   = EAG.nil;
        rep.Scope.End   = EAG.nil;
        rep.Formal      = EAG.ParamsDesc.init;
        this.hNont[anonSym].Def = rep;
        return anonSym;
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

        // Collect epsilon anonymous HNont indices in index order.
        int[] epsilonAnonymList;

        foreach (sym; EAG.firstHNont .. EAG.NextHNont)
            if (EAG.HNont[sym].Id < 0)
                epsilonAnonymList ~= sym;

        // Map named nonterminals.
        foreach (gammaSym; EAG.firstHNont .. cast(int) this.hNont.length)
        {
            if (this.hNont[gammaSym].anonymous)
                continue;

            const id = this.hNont[gammaSym].Id;
            int   epsilonSym = EAG.firstHNont;

            while (epsilonSym < EAG.NextHNont && EAG.HNont[epsilonSym].Id != id)
                ++epsilonSym;

            if (epsilonSym >= EAG.NextHNont)
            {
                error!"compareHyper: named HNont '%s' not found in EAG"(
                    EAG.symbolTable.symbol(id));
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

        // ----------------------------------------------------------------
        // Compare total HNont count.
        // ----------------------------------------------------------------
        if (cast(int) this.hNont.length != EAG.NextHNont)
        {
            error!"compareHyper: gamma has %s HNont entries but EAG has %s"(
                this.hNont.length, EAG.NextHNont);
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

            while (epsilonSym < EAG.NextHTerm && EAG.HTerm[epsilonSym].Id != id)
                ++epsilonSym;

            if (epsilonSym >= EAG.NextHTerm)
            {
                error!"compareHyper: HTerm '%s' not found in EAG"(
                    EAG.symbolTable.symbol(id));
                ++count;
            }
            else
            {
                gammaToHTerm[gammaSym] = epsilonSym;
            }
        }

        if (cast(int) this.hTerm.length != EAG.NextHTerm)
        {
            error!"compareHyper: gamma has %s HTerm entries but EAG has %s"(
                this.hTerm.length, EAG.NextHTerm);
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
                : EAG.symbolTable.symbol(this.hNont[gammaSym].Id);

            // ---- IsToken ----
            if (this.hNont[gammaSym].IsToken != EAG.HNont[epsilonSym].IsToken)
            {
                error!"compareHyper: HNont '%s' IsToken %s != %s"(
                    symName,
                    this.hNont[gammaSym].IsToken, EAG.HNont[epsilonSym].IsToken);
                ++count;
            }

            // ---- Def type ----
            const gammaHasDef   = this.hNont[gammaSym].Def !is null;
            const epsilonHasDef = EAG.HNont[epsilonSym].Def !is null;

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
            const epsIsGrp   = cast(EAG.Grp) EAG.HNont[epsilonSym].Def !is null;
            const epsIsRep   = cast(EAG.Rep) EAG.HNont[epsilonSym].Def !is null;
            const epsIsOpt   = cast(EAG.Opt) EAG.HNont[epsilonSym].Def !is null;

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
            EAG.Alt epsilonAlt = EAG.HNont[epsilonSym].Def.Sub;

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
                            const gammaName = EAG.symbolTable.symbol(this.hTerm[gammaTermSym].Id);

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
                                : EAG.symbolTable.symbol(this.hNont[gammaNontSym].Id);

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
        const id = cast(int) EAG.symbolTable.intern(name);

        if (auto p = id in this.mNontById)
            return *p;

        const sym = cast(int) this.mNont.length;

        this.mNont ~= EAG.MNontRecord(id, EAG.nil, EAG.nil, false);
        this.mNontById[id] = sym;
        return sym;
    }

    private int internMTerm(string name) @safe
    {
        const id = cast(int) EAG.symbolTable.intern(name);

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
        this.hNontNonterminal ~= nonterminal;

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
            const id = cast(int) EAG.symbolTable.intern(nonterminal.toString);

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
        const id = cast(int) EAG.symbolTable.intern(name);

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
        f.Actual = EAG.ParamsDesc.init; // filled in Phase 3c
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

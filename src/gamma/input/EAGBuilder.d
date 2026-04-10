module gamma.input.EAGBuilder;

import EAG = epsilon.eag;
import gamma.grammar.LhsNode;
import gamma.grammar.Nonterminal;
import gamma.grammar.SymbolNode;
import gamma.input.epsilang.analyzer : GammaEAG = EAG;
import log;

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

    this(GammaEAG eag)
    {
        this.eag = eag;

        // Reserve slot 0 in each array so real entries start at index 1
        this.mNont   = new EAG.MNontRecord[1];
        this.mTerm   = new EAG.MTermRecord[1];
        this.mAlt    = new EAG.MAltRecord[1];
        this.membBuf = new int[1];

        buildMeta;
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

    /**
     * Diff the builder's internal meta-grammar mirrors against the live EAG globals
     * (already populated by epsilon.analyzer.Analyse()) and log per-field mismatches.
     *
     * Returns: number of differences found (0 = perfect match)
     */
    int compare()
    {
        return compareMeta;
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
}

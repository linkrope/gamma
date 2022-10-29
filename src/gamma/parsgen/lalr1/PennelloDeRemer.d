module gamma.parsgen.lalr1.PennelloDeRemer;

import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.GrammarProperties;
import gamma.grammar.Node;
import gamma.grammar.Nonterminal;
import gamma.grammar.Rule;
import gamma.grammar.Symbol;
import gamma.grammar.SymbolNode;
import gamma.grammar.Terminal;
import gamma.parsgen.lalr1.LR1ConflictResolver;
import gamma.parsgen.lalr1.LR1ParserGenerator;
import gamma.parsgen.lalr1.LRItem;
import gamma.parsgen.lalr1.LRMachine;
import gamma.parsgen.lalr1.OrderedLR1Tables;
import gamma.parsgen.lalr1.SCCSetComputation;
import gamma.util.Indexed;
import gamma.util.Position;
import log;
import std.bitmanip : BitArray;

private alias State = LRMachine.State;

private alias Transition = LRMachine.Transition;

public void generateParser(Grammar grammar)
{
    import gamma.parsgen.lalr1.LR1ParserTablesWriter : write;
    import gamma.parsgen.lalr1.SimpleLR1ConflictResolver : SimpleLR1ConflictResolver;
    import std.stdio : File;

    const name = "parser-tables.json";
    auto parserGenerator = new PennelloDeRemer;
    auto conflictResolver = new SimpleLR1ConflictResolver(grammar);
    auto parserTables = parserGenerator.computeParser(grammar, conflictResolver);

    info!"writing %s"(name);
    write(parserTables, File(name, "w"));
}

/**
 * Implementation of Pennello's and DeRemer's efficient LALR(1) look-ahead computation algorithm
 * given an ("ordered") LR(0) machine.
 * Covers some extensions to equip the generated LR parsers with automatic error correction according to
 *
 *     J. Röhrich: "Methods for the Automatic Construction of Error Correcting Parsers",
 *     Acta Informatica 13, 115--139 (1980).
 *
 * @author SöKa
 */
public class PennelloDeRemer : LR1ParserGenerator
{
    private LR1ConflictResolver lr1ConflictResolver;

    private Grammar grammar;

    private GrammarProperties grammarProperties;

    private LRMachine lrMachine;

    private LRMachine.Transition[] nontTransitions;

    private BitArray[] followSet; // [nontTransition.index]

    private LRMachine.Transition[][] includes; // [nontTransition.index]

    private LookbackDependency[] lookback;

    private int[] lookbackIndex; // from=[2*state.index], to=[2*state.index+1]

    public OrderedLR1Tables computeParser(Grammar grammar, LR1ConflictResolver lr1ConflictResolver)
    {
        import std.format : format;

        this.grammar = grammar;
        this.lr1ConflictResolver = lr1ConflictResolver;

        checkGrammar;
        this.grammarProperties = new GrammarProperties(this.grammar);

        if (!this.grammarProperties.isReduced)
            warn!"parser grammar is not reduced";

        // TODO: compose single log message
        trace!"First productive alternatives:";
        foreach (nonterminal; grammar.nonterminals)
        {
            int i = 0;

            foreach (alternative; grammar.ruleOf(nonterminal).alternatives)
            {
                if (this.grammarProperties.isFirstProductiveAlternative(alternative))
                    trace!"#%s for lhs %s"(i, alternative.lhs.symbol);
                ++i;
            }
        }

        this.lrMachine = new LRMachine(this.grammar, this.grammarProperties);
        this.lrMachine.computeLR0Machine;

        initLAComputation;
        computeREAD;
        computeINCLUDES;
        computeFOLLOW;
        computeLOOKBACK;
        return computeParserTables;
    }

    /**
     * Checks whether this.grammar is acceptable for the parser generator.
     * <p>
     * The following checks are performed:<br>
     * (1) that this.grammar is a pure context-free grammar and <br>
     * (2) that this.grammar is an "extended" context-free grammar,
     * i.e. its start symbol &lt;ExtendedStartSymbol> has only one alternative
     * &lt;ExtendedStartSymbol> ::= &lt;StartSymbol> &lt;eofSymbol> such that
     * &lt;StartSymbol> and &lt;ExtendedStartSymbol> are Nonterminals, &lt;eofSymbol> is a Terminal,
     * and both &lt;ExtendedStartSymbol> and &lt;eofSymbol> occur only in this grammar rule.
     */
    private void checkGrammar()
    {
        Rule startRule = this.grammar.ruleOf(this.grammar.startSymbol);

        if (startRule.alternatives.length != 1)
            nonPositionMark("Not an extended grammar.");

        auto startAlt = cast(Alternative) startRule.alternatives[0];

        if (startAlt.rhs is null || startAlt.rhs.length != 2)
            nonPositionMark("Not an extended grammar.");
        if (!(cast(Nonterminal) (cast(SymbolNode) startAlt.rhs[0]).symbol))
            nonPositionMark("Not an extended grammar.");

        Symbol extendedStartSymbol = this.grammar.startSymbol;
        Symbol eofSymbol = (cast(SymbolNode) startAlt.rhs[1]).symbol;

        if (!(cast(Terminal) eofSymbol))
            nonPositionMark("Not an extended grammar.");

        foreach (rule; this.grammar.rules)
        {
            foreach (alternative; rule.alternatives)
            {
                if (alternative == startAlt)
                    continue;

                for (size_t i = 0, n = alternative.rhs.length; i < n; ++i)
                {
                    Node node = alternative.rhs[i];
                    if (!(cast(SymbolNode) node))
                    {
                        node.position.markError("Not a pure context-free grammar.");
                        return;
                    }

                    auto sn = cast(SymbolNode) node;

                    if (sn.symbol == extendedStartSymbol || sn.symbol == eofSymbol)
                        sn.position.markError("Not an extended grammar.");
                }
            }
        }
    }

    /**
     * Reports the given message as a "global" problem of this.grammar.
     * <p>
     * The problem is reported at the lhs SymbolNode of this.grammar.startSymbol's
     * first Alternative.
     * If that Position is null, it is expected that this.grammar is an extended
     * grammar and that the first SymbolNode of this.grammar.startSymbol's
     * first Alternative points, from a user's point of view, to the "actual" start
     * symbol of the grammar. So the problem is reported at that "actual" start symbol's
     * lhs SymbolNode of its first Alternative.
     * If this latter Position is also null, the given message is logged with Level.SEVERE.
     * @param message The problem description text.
     */
    private void nonPositionMark(string message)
    {
        if (this.grammar is null)
            return;

        Position pos;
        Alternative[] alts = this.grammar.ruleOf(this.grammar.startSymbol).alternatives;

        if (alts !is null && alts.length == 1)
            pos = alts[0].lhs.position;
        if (pos == Position())
        {
            Node[] rhs = alts[0].rhs;

            if (rhs !is null && rhs.length == 2 && cast(Nonterminal)(cast(SymbolNode) rhs[0]).symbol)
            {
                auto s = cast(Nonterminal)(cast(SymbolNode) rhs[0]).symbol;

                alts = this.grammar.ruleOf(s).alternatives;
                if (alts !is null)
                    pos = alts[0].lhs.position;
            }
        }

        if (pos != Position())
            pos.markError(message);
        else
            error!"%s"(message);
    }

    private void initLAComputation()
    {
        import std.conv : to;

        this.nontTransitions = lrMachine.getNontTransitions;

        int maxNontTransitionIndex = -1;

        foreach (i; 0 .. this.nontTransitions.length)
            if (this.nontTransitions[i].index.to!int > maxNontTransitionIndex)
                maxNontTransitionIndex = this.nontTransitions[i].index.to!int;

        this.followSet = new BitArray[maxNontTransitionIndex + 1];
        this.includes = new LRMachine.Transition[][maxNontTransitionIndex + 1];
        foreach (i; 0 .. this.nontTransitions.length)
        {
            LRMachine.Transition t = this.nontTransitions[i];

            this.followSet[t.index].length = this.grammar.terminals.length;
            this.includes[t.index] = null;
        }
    }

    /**
     * Computes the "read" relation which associates nonterminal transitions
     * and (look-ahead) terminal symbols.
     * <p>
     * read = reads* directly-reads.
     */
    private void computeREAD()
    {
        import std.algorithm : map;
        import std.array : array;

        // "reads" relation to be traversed by the SCCSetComputation algorithm
        auto readsRelation = new class SCCSetComputation.TransitionEnumerator
        {
            public void visitNeighborsOf(Indexed nontTrans, SCCSetComputation.TransitionWalker walker)
            {
                    // The "reads" relation is computed on demand.
                LRMachine.State q = (cast(LRMachine.Transition) nontTrans).to;

                if (q.outgoing !is null)
                {
                    for (size_t i = 0, n = q.outgoing.length; i < n; ++i)
                    {
                        LRMachine.Transition xTrans = q.outgoing[i];
                        Symbol x = xTrans.label;

                        if (cast(Nonterminal) x && grammarProperties.isNullable(x))
                            walker.walk(nontTrans, xTrans);
                    }
                }
            }
        };

        // Set operations for the computation of the "reads" sets
        auto readSetOps = new class SCCSetComputation.SetOperator
        {
            public void initSet(Indexed nontTrans)
            {
                // Compute the set of terminals (index) which the LR machine's
                // nonterminal transition nontTrans "directly-reads".
                LRMachine.State q = (cast(LRMachine.Transition) nontTrans).to;

                if (q.outgoing !is null)
                {
                    for (size_t i = 0, n = q.outgoing.length; i < n; ++i)
                    {
                        Symbol x = q.outgoing[i].label;

                        if (cast(Terminal) x)
                            this.outer.followSet[nontTrans.index][(cast(Terminal) x).index] = true;
                    }
                }
            }

            public void includeSet(Indexed nontTrans1, Indexed nontTrans2)
            {
                this.outer.followSet[nontTrans1.index] |= this.outer.followSet[nontTrans2.index];
            }
        };

        Indexed[] nodes = this.nontTransitions
            .map!(transition => cast(Indexed) transition)
            .array;

        SCCSetComputation.computeSets(nodes, readsRelation, readSetOps);
    }

    /**
     * Computes the "includes" relation.
     */
    private void computeINCLUDES()
    {
        for (size_t i = 0, m = this.nontTransitions.length; i < m; ++i)
        {
            LRMachine.Transition qTrans = nontTransitions[i];
            LRMachine.State q = qTrans.from;
            auto lhs = cast(Nonterminal) qTrans.label;

            foreach (alternative; this.grammar.ruleOf(lhs).alternatives)
            {
                Node[] rhs = alternative.rhs;
                size_t k = 0, n = rhs.length;

                while (k < n)
                {
                    Symbol x = (cast(SymbolNode) rhs[n - k - 1]).symbol;
                    if (cast(Terminal) x)
                        break;
                    ++k;
                    if (!grammarProperties.isNullable(x))
                        break;
                }
                if (k > 0)
                {
                    LRMachine.State p;
                    int j;

                    for (j = 0, p = q; j < n - k; ++j)
                        p = lrMachine.getTransition(p, (cast(SymbolNode) rhs[j]).symbol).to;
                    for (; j < n; ++j)
                    {
                        LRMachine.Transition pTrans =
                            lrMachine.getTransition(p, (cast(SymbolNode) rhs[j]).symbol);

                        // pTrans includes qTrans
                        this.includes[pTrans.index] ~= qTrans;
                        p = pTrans.to;
                    }
                }
            }
        }
    }

    /**
     * Computes the "follow" relation, which associates nonterminal transitions
     * and (look-ahead) terminal symbols.
     * <p>
     * follow = includes* reads* directly-reads.
     */
    private void computeFOLLOW()
    {
        import std.algorithm : map;
        import std.array : array;

        // "includes" relation to be traversed by the SCCSetComputation algorithm
        auto includesRelation = new class SCCSetComputation.TransitionEnumerator
        {
            public void visitNeighborsOf(Indexed nontTrans, SCCSetComputation.TransitionWalker walker)
            {
                foreach (transition; this.outer.includes[nontTrans.index])
                {
                    walker.walk(nontTrans, transition);
                }
            }
        };

        // Set operations for the computation of the "follow" sets
        auto followSetOps = new class SCCSetComputation.SetOperator
        {
            public void initSet(Indexed nontTrans)
            {
                    // "follow" Set initialization already done!
            }

            public void includeSet(Indexed nontTrans1, Indexed nontTrans2)
            {
                this.outer.followSet[nontTrans1.index] |= this.outer.followSet[nontTrans2.index];
            }
        };

        Indexed[] nodes = this.nontTransitions
            .map!(transition => cast(Indexed) transition)
            .array;

        SCCSetComputation.computeSets(nodes, includesRelation, followSetOps);
    }

    /**
     * An instance captures a dependency of the "lookback" relation such that
     * <p>
     * (state, alternative) lookback nontTransition.
     */
    private class LookbackDependency
    {
        private LRMachine.State state;

        private Alternative alternative;

        private LRMachine.Transition nontTransition;

        this(LRMachine.State state, Alternative alternative, LRMachine.Transition nontTransition)
        {
            this.state = state;
            this.alternative = alternative;
            this.nontTransition = nontTransition;
        }
    }

    /**
     * Computes the "lookback" relation which has to be combined with the "follow"
     * relation to yield the "has-LALR-lookahead" relation. "lookback" associates
     * (LR(0) state, alternative) pairs and nonteminal transitions whereas
     * "has-LALR-lookahead" associates (LR(0) state, alternative) pairs and
     * (look-ahead) terminal symbols.
     * <p>
     * has-LALR-lookahead = lookback includes* reads* directly-reads.
     */
    private void computeLOOKBACK()
    {
        import std.algorithm : sort, SwapStrategy;

        LookbackDependency[] lookback;

        for (size_t i = 0, m = nontTransitions.length; i < m; ++i)
        {
            LRMachine.Transition qTrans = nontTransitions[i];
            LRMachine.State q = qTrans.from;
            auto lhs = cast(Nonterminal) qTrans.label;

            foreach (alternative; this.grammar.ruleOf(lhs).alternatives)
            {
                Node[] rhs = alternative.rhs;
                LRMachine.State p = q;

                for (size_t j = 0, n = rhs.length; j < n; ++j)
                    p = lrMachine.getTransition(p, (cast(SymbolNode) rhs[j]).symbol).to;
                lookback ~= new LookbackDependency(p, alternative, qTrans);
            }
        }

        this.lookback = lookback;

        int lookbackPartitioner(LookbackDependency lb1, LookbackDependency lb2)
        {
            import std.conv : to;

            int result = lb1.state.index.to!int - lb2.state.index.to!int;

            if (result == 0)
                result = cast(int) lb1.toHash - cast(int) lb2.toHash; // .index would be better
            return result;
        }

        this.lookback.sort!((a, b) => lookbackPartitioner(a, b) < 0, SwapStrategy.stable);
        this.lookbackIndex = new int[2 * lrMachine.getStates.length];
        this.lookbackIndex[] = -1;

        int i = 0;

        while (i < this.lookback.length)
        {
            LRMachine.State s = this.lookback[i].state;
            this.lookbackIndex[2 * s.index] = i;

            int j = i + 1;

            while (j < this.lookback.length && this.lookback[j].state == s)
                ++j;
            this.lookbackIndex[2 * s.index + 1] = j;
            i = j;
        }

    }

    private BitArray lalrLookaheadsFor(LRItem item, LRMachine.State state)
    {
        BitArray lalrLookaheads;
        int k1 = this.lookbackIndex[2 * state.index];
        int k2 = this.lookbackIndex[2 * state.index + 1];

        lalrLookaheads.length = this.grammar.terminals.length;
        for (int k = k1; k < k2; ++k)
            if (this.lookback[k].alternative == item.alt)
                lalrLookaheads |= this.followSet[lookback[k].nontTransition.index];
        return lalrLookaheads;
    }

    /**
     * Computes the shift and reduce actions of the resulting canonical LALR(1) parser.
     */
    private OrderedLR1Tables computeParserTables()
    {
        State[] states = this.lrMachine.getStates;
        OrderedLR1Tables.Action[] parserActionRow = new OrderedLR1Tables.Action[grammar.terminals.length];
        size_t[] parserActionRowNext = new size_t[grammar.terminals.length + 1];
        size_t[] parserActionRowPrev = new size_t[grammar.terminals.length + 1];
        size_t HEAD = grammar.terminals.length;

        return new class (grammar) OrderedLR1Tables
        {
            private Grammar grammar_;

            private Action[][] parserActionRows;

            private Goto[][] gotoRows;

            private Terminal eofSymbol;

            this(Grammar grammar)
            {
                this.grammar_ = grammar;
                this.parserActionRows = new Action[][states.length];
                this.gotoRows = new Goto[][states.length];
                this.eofSymbol = cast(Terminal)
                    (cast(SymbolNode)(cast(Alternative) grammar.ruleOf(grammar.startSymbol).alternatives[0]).rhs[1])
                    .symbol;
            }

            public Grammar grammar()
            {
                return this.grammar_;
            }

            public size_t stateCount()
            {
                return states.length;
            }

            public Terminal eof()
            {
                return eofSymbol;
            }

            private void unlinkFromParserActionList(size_t lookaheadIndex)
            {
                parserActionRowNext[parserActionRowPrev[lookaheadIndex]] = parserActionRowNext[lookaheadIndex];
                parserActionRowPrev[parserActionRowNext[lookaheadIndex]] = parserActionRowPrev[lookaheadIndex];
            }

            private void prependToParserActionList(size_t lookaheadIndex)
            {
                parserActionRowNext[lookaheadIndex] = parserActionRowNext[HEAD];
                parserActionRowPrev[lookaheadIndex] = parserActionRowPrev[parserActionRowNext[HEAD]];
                parserActionRowPrev[parserActionRowNext[HEAD]] = lookaheadIndex;
                parserActionRowNext[HEAD] = lookaheadIndex;
            }

            private void enterReduce(size_t stateIndex, Alternative alt, Terminal lookahead)
            {
                size_t lookaheadIndex = lookahead.index;

                if (cast(OrderedLR1Tables.Reduce) parserActionRow[lookaheadIndex])
                {
                    auto reduce = cast(OrderedLR1Tables.Reduce) parserActionRow[lookaheadIndex];
                    Alternative origAlt = reduce.alternative;

                    if (alt != origAlt)
                    {
                        Object o = lr1ConflictResolver.resolveReduceReduceConflict(origAlt, alt,
                            grammar.terminal(lookaheadIndex),
                            stateIndex);

                        if (o == alt)
                        {
                            // action already entered; prepend anew (1st in list -> continuation!)
                            unlinkFromParserActionList(lookaheadIndex);
                            prependToParserActionList(lookaheadIndex);
                            reduce.alternative = alt;
                        }
                        else if (o != origAlt)
                        {
                            unlinkFromParserActionList(lookaheadIndex);
                            parserActionRow[lookaheadIndex] = null;
                        }
                    }
                }
                else if (cast(OrderedLR1Tables.Shift) parserActionRow[lookaheadIndex])
                {
                    auto shift = cast(OrderedLR1Tables.Shift) parserActionRow[lookaheadIndex];
                    Object o = lr1ConflictResolver.resolveShiftReduceConflict(shift.lookahead, alt, stateIndex);

                    if (o != shift.lookahead)
                    {
                        if (o == alt)
                        {
                            unlinkFromParserActionList(lookaheadIndex);
                            prependToParserActionList(lookaheadIndex);
                            parserActionRow[lookaheadIndex] =
                                new OrderedLR1Tables.Reduce(grammar.terminal(lookaheadIndex), alt);
                        }
                        else
                        {
                            unlinkFromParserActionList(lookaheadIndex);
                            parserActionRow[lookaheadIndex] = null;
                        }
                    }
                }
                else if (parserActionRow[lookaheadIndex] !is null)
                {
                    // (parserActionRow[lookaheadIndex] instanceof OrderedLR1Tables.Halt)
                    lr1ConflictResolver.noteHaltConflictOn(alt, stateIndex);
                    unlinkFromParserActionList(lookaheadIndex);
                    prependToParserActionList(lookaheadIndex);
                    parserActionRow[lookaheadIndex] = new OrderedLR1Tables.Halt(eof);
                }
                else
                {
                    // (parserActionRow[lookaheadIndex] is null)
                    parserActionRow[lookaheadIndex] =
                        new OrderedLR1Tables.Reduce(grammar.terminal(lookaheadIndex), alt);
                    prependToParserActionList(lookaheadIndex);
                }
            }

            private void enterShift(size_t stateIndex, Terminal lookahead, size_t toStateIndex)
            {
                size_t lookaheadIndex = lookahead.index;
                OrderedLR1Tables.Action action = parserActionRow[lookaheadIndex];

                if (cast(OrderedLR1Tables.Shift) action)
                {
                    // action already entered; prepend anew (1st in list -> continuation!)
                    unlinkFromParserActionList(lookaheadIndex);
                    prependToParserActionList(lookaheadIndex);
                }
                else if (parserActionRow[lookaheadIndex] !is null)
                {
                    // parserActionRow[lookaheadIndex] instanceof OrderedLR1Tables.Reduce
                    auto reduce = cast(OrderedLR1Tables.Reduce) parserActionRow[lookaheadIndex];
                    Alternative origAlt = reduce.alternative;
                    Object o = lr1ConflictResolver.resolveShiftReduceConflict(lookahead, origAlt, stateIndex);

                    if (o == lookahead)
                    {
                        unlinkFromParserActionList(lookaheadIndex);
                        prependToParserActionList(lookaheadIndex);
                        parserActionRow[lookaheadIndex] = new OrderedLR1Tables.Shift(lookahead, toStateIndex);
                    }
                    else if (o != origAlt)
                    {
                        unlinkFromParserActionList(lookaheadIndex);
                        parserActionRow[lookaheadIndex] = null;
                    }
                }
                else
                {
                    // (parserActionRow[lookaheadIndex] is null)
                    parserActionRow[lookaheadIndex] = new OrderedLR1Tables.Shift(lookahead, toStateIndex);
                    prependToParserActionList(lookaheadIndex);
                }
            }

            private void enterHalt(size_t stateIndex)
            {
                size_t lookaheadIndex = eof.index; // PROBLEM!! eof not part of original grammar; eof.index??

                if (parserActionRow[lookaheadIndex] !is null)
                {
                    // cast(OrderedLR1Tables.Reduce) parserActionRow[lookaheadIndex]
                    auto reduce = cast(OrderedLR1Tables.Reduce) parserActionRow[lookaheadIndex];
                    Alternative origAlt = reduce.alternative;

                    lr1ConflictResolver.noteHaltConflictOn(origAlt, stateIndex);
                    unlinkFromParserActionList(lookaheadIndex);
                }
                parserActionRow[lookaheadIndex] = new OrderedLR1Tables.Halt(eof);
                prependToParserActionList(lookaheadIndex);
            }

            public Action[] getSortedParserActionRow(size_t stateIndex)
            {
                if (parserActionRows[stateIndex] !is null)
                    return parserActionRows[stateIndex];

                auto state = cast(LRMachine.State) states[stateIndex];

                parserActionRow[] = null;
                parserActionRowNext[] = -1;
                parserActionRowPrev[] = -1;
                parserActionRowNext[HEAD] = HEAD; // doubly linked list of ...
                parserActionRowPrev[HEAD] = HEAD; // ... parserActionRow[] entries

                // Make parser action table entries in reverse order of items in ordered item list
                for (size_t i = state.orderedClosureItems.length; i > 0; --i)
                {
                    LRItem item = state.orderedClosureItems[i - 1];

                    if (item.complete)
                    {
                        BitArray bs = this.outer.lalrLookaheadsFor(item, state);

                        foreach (t; bs.bitsSet)
                            enterReduce(state.index, item.alt, grammar.terminal(t));
                    }
                    else if (item.symbolBehindDot == eof)
                        enterHalt(state.index);
                    else if (cast(Terminal) item.symbolBehindDot)
                        enterShift(state.index,
                            cast(Terminal) item.symbolBehindDot,
                            lrMachine.getTransition(state, item.symbolBehindDot).to.index);
                }
                // Set Action.isContinuationAction field(s) in second pass
                size_t ca = parserActionRowNext[HEAD];

                if (ca != HEAD)
                {
                    if (cast(OrderedLR1Tables.Reduce) parserActionRow[ca])
                    {
                        auto reduce = cast(OrderedLR1Tables.Reduce) parserActionRow[ca];
                        Alternative alt = reduce.alternative;

                        for (; ca != HEAD; ca = parserActionRowNext[ca])
                        {
                            OrderedLR1Tables.Action a = parserActionRow[ca];
                            if (cast(OrderedLR1Tables.Reduce) a
                                && (cast(OrderedLR1Tables.Reduce) a).alternative == alt)
                                a.isContinuationAction = true;
                        }
                    }
                    else
                        parserActionRow[ca].isContinuationAction = true;
                }

                Action[] rowAsList;

                for (size_t t = 0; t < parserActionRow.length; ++t)
                    if (parserActionRow[t] !is null)
                        rowAsList ~= parserActionRow[t];
                parserActionRows[stateIndex] = rowAsList;
                return parserActionRows[stateIndex];
            }

            public Goto[] getSortedGotoRow(size_t stateIndex)
            {
                if (gotoRows[stateIndex] !is null)
                    return gotoRows[stateIndex];

                auto state = cast(LRMachine.State) states[stateIndex];

                Goto[] rowAsList;

                // Output nonterminal transitions
                if (state.outgoing !is null)
                {
                    for (size_t i = 0; i < state.outgoing.length; ++i)
                    {
                        LRMachine.Transition transition = state.outgoing[i];

                        if (cast(Nonterminal) transition.label)
                        {
                            rowAsList ~=
                                new OrderedLR1Tables.Goto(cast(Nonterminal) transition.label, transition.to.index);
                        }
                    }
                }
                gotoRows[stateIndex] = rowAsList;
                return gotoRows[stateIndex];
            }
        };
    }
}

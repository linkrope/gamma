module gamma.parsgen.lalr1.LRMachine;

import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.GrammarProperties;
import gamma.grammar.Nonterminal;
import gamma.grammar.Rule;
import gamma.grammar.Symbol;
import gamma.grammar.SymbolNode;
import gamma.grammar.Terminal;
import gamma.parsgen.lalr1.LRItem;
import gamma.util.Indexed;
import log;

/**
 * Computes an LR(0) machine from a given context-free grammar.
 * The resulting LR(0) machine is "ordered" in the sense of
 *
 *     J. Röhrich: "Methods for the Automatic Construction of Error Correcting Parsers",
 *     Acta Informatica 13, 115--139 (1980).
 *
 * @author SöKa
 */
class LRMachine
{
    private Grammar grammar;

    private GrammarProperties grammarProperties;

    private Transition[] transitions; // Transition elements

    private Transition[] ntTransitions; // Transition elements

    private State[] states; // State elements

    private State[State] hashedStates; // HashMap of objects in states (mapped to themselves)

    private LRItem[][] items; // [lhs.index][alt#]

    private int nextItemId;

    private bool[] itemTraversed;

    Transition[] getNontTransitions()
    {
        return ntTransitions.dup;
    }

    Transition[] getTransitions()
    {
        return transitions.dup;
    }

    Transition getTransition(State state, Symbol label)
    {
        foreach (transition; state.outgoing)
            if (transition.label == label)
                return transition;
        return null;
    }

    /**
     * Returns an unmodifiable List of the computed LR(0) machine's LRMachine.State
     * objects. All states in this List are guaranteed to have distinct index values
     * 0..(<i>n</i>-1) where <i>n</i> is the number of states in the List,
     * and each state's index reflects the state's position in the List.
     */
    State[] getStates()
    {
        return states.dup;
    }

    private interface LRItemProcessor
    {
        void process(LRItem item);
    }

    class State : Indexed
    {
        size_t index_; // set when state is added to the lrMachine's state list

        LRItem[] kernelItems;

        LRItem[] orderedClosureItems;

        Transition[] outgoing;

        this(LRItem[] kernelItems)
        {
            // Caller guarantees that (ordered) kernelItems[] of this state contain no duplicates!
            this.index_ = -1;
            this.kernelItems = kernelItems;
            this.orderedClosureItems = null;
            this.outgoing = null;
        }

        public size_t index() const
        {
            return this.index_;
        }

        public override bool opEquals(Object x) const
        {
            if (!cast(State) x)
                return false;

            State s = cast(State) x;

            if (this.kernelItems.length != s.kernelItems.length)
                return false;
            for (size_t i = 0, n = this.kernelItems.length; i < n; ++i)
                if (this.kernelItems[i] != s.kernelItems[i])
                    return false;
            return true;
        }

        public override size_t toHash() const
        {
            size_t hc = this.kernelItems.length;

            for (size_t i = 0, n = this.kernelItems.length; i < n; ++i)
                hc = (hc * 379 + this.kernelItems[i].index) % 13579;
            return hc;
        }

        private void forEachOrderedClosureItem0(LRItem item, LRItemProcessor itemProcessor)
        {
            itemTraversed[item.index] = true;

            itemProcessor.process(item);

            // Recursively depth-first process closure items for item. Enumeration of closure items is according to
            //
            //   J. Röhrich: "Methods for the Automatic Construction of Error Correcting Parsers",
            //   Acta Informatica 13, 115--139 (1980)
            //
            // such that the closure item belonging to the continuation grammar precedes the other closure items.
            if (cast(Nonterminal) item.symbolBehindDot)
            {
                LRItem [] closureItems = this.outer.items[(cast(Nonterminal) item.symbolBehindDot).index];

                for (size_t j = 0, n = closureItems.length; j < n; ++j)
                {
                    if (closureItems[j].altIsInContinuationGrammar && !itemTraversed[closureItems[j].index])
                        forEachOrderedClosureItem0(closureItems[j], itemProcessor);
                }
                for (size_t j = 0, n = closureItems.length; j < n; ++j)
                {
                    if (!closureItems[j].altIsInContinuationGrammar && !itemTraversed[closureItems[j].index])
                        forEachOrderedClosureItem0(closureItems[j], itemProcessor);
                }
            }
        }

        void forEachOrderedClosureItem(LRItemProcessor itemProcessor)
        {
            itemTraversed[] = false;

            for (size_t i = 0, m = this.kernelItems.length; i < m; ++i)
            {
                // process kernel item
                forEachOrderedClosureItem0(this.kernelItems[i], itemProcessor);
            }
        }

        void computeTransitions()
        {
            import std.algorithm : sort, SwapStrategy;

            /*
             * Compute ordered closure of this.kernelItems[].
             * Note that this.kernelItems[] contains no duplicate items,
             * and that the "ordered closure" algorithm will, therefore, also produce no duplicates!
             */
            LRItem[] orderedClosureItemList;

            forEachOrderedClosureItem(
                new class LRItemProcessor
                {
                    public void process(LRItem item)
                    {
                        orderedClosureItemList ~= item;
                    }
                }
                );
            this.orderedClosureItems = cast(LRItem []) orderedClosureItemList;

            trace!"state %s%-(\n%s%)"(index, this.orderedClosureItems);

            /*
             * Move dot right in all (ordered) items of this state; collect the resulting items,
             * and sort them by access symbol.
             * The number of outgoing transitions can be computed from the result.
             */
            LRItem[] newItems;

            for (size_t i = 0, n = this.orderedClosureItems.length; i < n; ++i)
            {
                if (!orderedClosureItems[i].complete)
                    newItems ~= orderedClosureItems[i].nextItem;
            }

            /*
             * Any new states / item sets at all?
             */
            if (newItems.length == 0)
                return;

            /*
             * Sort items in newItems[] by access symbol, then by whether the item's dotted
             * alternatives belong to the chosen Röhrich continuation grammar or not, and
             * finally by index.
             * We rely on the fact that the Arrays.sort(Object[], Comparator) algorithm is a
             * "stable" sort, i.e. it does not change the order of equal members w.r.t. the
             * given Comparator.
             */
            LRItem[] sortedItems = cast(LRItem []) newItems;

            sortedItems.sort!((a, b) => itemSetPartitioner(a, b) < 0, SwapStrategy.stable);

            /*
             * Now inspect the items. Groups of them belong to one target state, and there
             * are no duplicate items. Check if target state is new or already known (kernel
             * items suffice for this check). Build corresponding Transition objects and put
             * them into the vector of outgoing transitions.
             */
            int m = 0;

            for (size_t i = 0, n = sortedItems.length; i < n;)
            {
                size_t i0 = i;
                Symbol accessSymbol = sortedItems[i].symbolPrecedingDot;

                ++i;
                while (i < n && sortedItems[i].symbolPrecedingDot == accessSymbol)
                    ++i;

                LRItem[] newKernelItems = new LRItem[i - i0];

                newKernelItems[0 .. i - i0] = sortedItems[i0 .. i];
                State toState = new State(newKernelItems);

                // Lookup hashedStates to see if toState is a known state
                State toState1 = hashedStates.get(toState, null);

                if (toState1 is null)
                    addState(toState);
                else
                    toState = toState1;

                trace!"GOTO(%s, %s) = %s"(this.index, accessSymbol, toState.index);

                addTransition(new Transition(transitions.length, this, toState, accessSymbol));
                ++m;
            }

            this.outgoing = new Transition [m];
            for (size_t i = 0, j = transitions.length - m; i < m; ++i, ++j)
                this.outgoing[i] = transitions[j];
        }

        private void print()
        {
            trace!"state %s%-(\n%s%)"(index, orderedClosureItems);
        }
    }

    class Transition : Indexed
    {
        const size_t index_;

        State from;

        State to;

        Symbol label;

        this(size_t index, State from, State to, Symbol label)
        {
            this.index_ = index;
            this.from = from;
            this.to = to;
            this.label = label;
        }

        public size_t index() const
        {
            return this.index_;
        }
    }

    this(Grammar grammar, GrammarProperties grammarProperties)
    {
        this.grammar = grammar;
        this.grammarProperties = grammarProperties;
    }

    void computeLR0Machine()
    {
        this.nextItemId = 0;

        this.transitions = null;
        this.ntTransitions = null;
        this.states = null;
        hashedStates = null;

        // Generate all LR(0) items
        this.items = new LRItem[][this.grammar.nonterminals.length];
        foreach (lhs; this.grammar.nonterminals)
        {
            Rule rule = this.grammar.ruleOf(lhs);
            this.items[lhs.index] = new LRItem[rule.alternatives.length];
            for (size_t i = 0, n2 = rule.alternatives.length; i < n2; ++i)
            {
                Alternative alt = rule.alternatives[i];
                LRItem item = null;

                for (size_t j = alt.rhs.length + 1; j > 0; --j)
                    item = new LRItem(this.nextItemId++, alt,
                        grammarProperties.isFirstProductiveAlternative(alt), j - 1, item);
                this.items[lhs.index][i] = item;
            }
        }

        this.itemTraversed = new bool[numberOfItems];
        addState(initialState);
        for (int stateNumber = 0; stateNumber < this.states.length; ++stateNumber)
        {
            State state = this.states[stateNumber];
            state.computeTransitions;
        }
        this.itemTraversed = null;

        // Unfortunately, we cannot drop all items and item sets here (as we could
        // with Pennello/DeRemer's original algorithm) because output generation
        // according to Röhrich error handling and caller-controlled conflict
        // resolution require that we keep ordered item lists at the states.
    }

    private State initialState()
    {
        LRItem[] kernelItems = [this.items[grammar.startSymbol.index][0]];

        return new State(kernelItems);
    }

    private void addTransition(Transition transition)
    {
        this.transitions ~= transition;
        if (cast(Nonterminal) transition.label)
            this.ntTransitions ~= transition;
    }

    private void addState(State state)
    {
        state.index_ = this.states.length;
        this.states ~= state;
        this.hashedStates[state] = state;
    }

    private int numberOfItems()
    {
        return this.nextItemId;
    }

//    private LRItem shiftedDotItemOf(LRItem item)
//    {
//        return item.nextItem;
//    }
}

private int itemSetPartitioner(LRItem i1, LRItem i2)
{
    import std.conv : to;

    if (i1.symbolPrecedingDot !is null && i2.symbolPrecedingDot !is null
        && i1.symbolPrecedingDot != i2.symbolPrecedingDot)
    {
        int n1;
        int n2;

        if (cast(Terminal) i1.symbolPrecedingDot)
            n1 = - (cast(Terminal) i1.symbolPrecedingDot).index.to!int - 1;
        else
            n1 = (cast(Nonterminal) i1.symbolPrecedingDot).index.to!int;
        if (cast(Terminal) i2.symbolPrecedingDot)
            n2 = - (cast(Terminal) i2.symbolPrecedingDot).index.to!int - 1;
        else
            n2 = (cast(Nonterminal) i2.symbolPrecedingDot).index.to!int;
        return n1 - n2;
    }

    return 0;
}

@("compute LR(0) machine")
unittest
{
    import gamma.grammar.GrammarBuilder : TestGrammarBuilder;
    import std.conv : to;

    with (TestGrammarBuilder())
    {
        rule("G: E = E | f");
        rule("E: T | E + T");
        rule("T: f | T * f");

        auto grammarProperties = new GrammarProperties(grammar);

        with (new LRMachine(grammar, grammarProperties))
        {
            computeLR0Machine;

            auto states = getStates;

            assert(states.length == 10);
            // state 0
            assert(states[0].orderedClosureItems.to!(string[]) ==
                [
                    `G -> . E "=" E`,
                    `E => . T`,
                    `T => . f`,
                    `T -> . T "*" f`,
                    `E -> . E "+" T`
                ]);
            assert(getTransition(states[0], symbol("f")).to == states[1]);
            assert(getTransition(states[0], symbol("E")).to == states[2]);
            assert(getTransition(states[0], symbol("T")).to == states[3]);
            // state 1
            assert(states[1].orderedClosureItems.to!(string[]) ==
                [
                    `T => f .`,
                ]);
            // state 2
            assert(states[2].orderedClosureItems.to!(string[]) ==
                [
                    `G -> E . "=" E`,
                    `E -> E . "+" T`,
                ]);
            assert(getTransition(states[2], symbol("+")).to == states[4]);
            assert(getTransition(states[2], symbol("=")).to == states[5]);
            // state 3
            assert(states[3].orderedClosureItems.to!(string[]) ==
                [
                    `E => T .`,
                    `T -> T . "*" f`,
                ]);
            assert(getTransition(states[3], symbol("*")).to == states[6]);
            // state 4
            assert(states[4].orderedClosureItems.to!(string[]) ==
                [
                    `E -> E "+" . T`,
                    `T => . f`,
                    `T -> . T "*" f`,
                ]);
            assert(getTransition(states[4], symbol("f")).to == states[1]);
            assert(getTransition(states[4], symbol("T")).to == states[7]);
            // state 5
            assert(states[5].orderedClosureItems.to!(string[]) ==
                [
                    `G -> E "=" . E`,
                    `E => . T`,
                    `T => . f`,
                    `T -> . T "*" f`,
                    `E -> . E "+" T`,
                ]);
            assert(getTransition(states[5], symbol("f")).to == states[1]);
            assert(getTransition(states[5], symbol("E")).to == states[8]);
            assert(getTransition(states[5], symbol("T")).to == states[3]);
            // state 6
            assert(states[6].orderedClosureItems.to!(string[]) ==
                [
                    `T -> T "*" . f`,
                ]);
            assert(getTransition(states[6], symbol("f")).to == states[9]);
            // state 7
            assert(states[7].orderedClosureItems.to!(string[]) ==
                [
                    `E -> E "+" T .`,
                    `T -> T . "*" f`,
                ]);
            assert(getTransition(states[7], symbol("*")).to == states[6]);
            // state 8
            assert(states[8].orderedClosureItems.to!(string[]) ==
                [
                    `G -> E "=" E .`,
                    `E -> E . "+" T`,
                ]);
            assert(getTransition(states[8], symbol("+")).to == states[4]);
            // state 9
            assert(states[9].orderedClosureItems.to!(string[]) ==
                [
                    `T -> T "*" f .`,
                ]);
        }
    }
}

module gamma.grammar.Nonterminal;

import gamma.grammar.Symbol;
import gamma.util.Indexed;

public class Nonterminal : Symbol, Indexed
{
	  private const size_t index_;

    /**
     * Creates a grammar nonterminal with the given name.
     *
     * @param representation the name of the nonterminal
     * @param index the index of the nonterminal, must be unique in
     * the set of all nonterminals of the grammar and
     * must not be greater than the number of nonterminals in the grammar
     */
    public this(string representation, size_t index)
    {
      super(representation);
      this.index_ = index;
    }

    /**
     * Returns the index of the nonterminal.
     * The index is unique in the set of all nonterminals of the grammar.
     * It cannot be greater than the number of nonterminals in the grammar
     * @return the unique index of the nonterminal
     */
    public size_t index() const
      {
      return this.index_;
    }
}

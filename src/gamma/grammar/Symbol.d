module gamma.grammar.Symbol;

public abstract class Symbol
{
	private string representation;

	protected this(string representation)
	{
		this.representation = representation;
	}

	public override string toString() const
	{
		return this.representation;
	}
}

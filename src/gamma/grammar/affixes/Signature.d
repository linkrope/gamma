module gamma.grammar.affixes.Signature;

import gamma.grammar.affixes.Mode;
import gamma.grammar.Nonterminal;
import gamma.util.Position;
import std.range;

public class Signature
{
	private const Mode[] modes_;

	private Nonterminal[] domains_;

	private Position position_;

	public this(Mode[] modes, Nonterminal[] domains, Position position)
	in (modes.length == domains.length)
	{
		this.modes_ = modes.dup;
		this.domains_ = domains.dup;
		this.position_ = position;
	}

	public this(Position position)
	{
		this.modes_ = null;
		this.position_ = position;
	}

	public override string toString() const
	{
		import std.array : appender;
		import std.conv : to;

		auto buffer = appender!string();

		buffer.put('<');
		foreach (i; 0 .. length)
		{
			if (i > 0)
				buffer.put(", ");
			buffer.put(this.modes_[i].to!string);
			buffer.put(' ');
			buffer.put(this.domains_[i].toString);
		}
		buffer.put('>');
		return buffer[];
	}

	public size_t length() const
	{
		return this.domains_.length;
	}

	public bool isEmpty() const
	{
		return this.domains_.empty;
	}

	public const(Mode)[] modes() const
	{
		return this.modes_;
	}

	public Nonterminal[] domains()
	{
		return this.domains_;
	}

	public Position position()
	{
		return this.position_;
	}
}

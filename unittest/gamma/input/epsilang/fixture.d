module gamma.input.epsilang.fixture;

import gamma.grammar.hyper.HyperGrammar : HyperGrammar;
import gamma.input.epsilang.parser : Parser;
import io : Input;

auto fixture() => Fixture(0);

struct Fixture
{
    import log : Level, logger;

    Parser parser;

    HyperGrammar hyperGrammar;

    this(int)
    {
        logger.clear;
    }

    ref Fixture parse(string source)
    {
        this.parser = new Parser(Input("test.eag", source));

        this.parser.parseSpecification;
        this.hyperGrammar = this.parser.buildHyperGrammar;
        return this;
    }

    void pass()
    {
        assert(this.parser.getErrorCount == 0);
        assert(this.hyperGrammar !is null);
    }

    void fail()
    {
        assert(this.parser.getErrorCount > 0 || this.hyperGrammar is null);
    }

    string[] diagnostics()
    {
        import std.algorithm : filter, map;
        import std.array : array;

        return logger.entries
            .filter!(entry => entry.level == Level.error)
            .map!(entry => entry.message)
            .array;
    }
}

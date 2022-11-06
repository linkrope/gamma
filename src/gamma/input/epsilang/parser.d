module gamma.input.epsilang.parser;

import epsilon.lexer;
import gamma.grammar.affixes.Variable;
import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.GrammarBuilder;
import gamma.grammar.hyper.Group;
import gamma.grammar.hyper.HyperSymbolNode;
import gamma.grammar.hyper.Operator;
import gamma.grammar.hyper.Option;
import gamma.grammar.hyper.Params;
import gamma.grammar.hyper.Repetition;
import gamma.grammar.hyper.RepetitionAlternative;
import gamma.grammar.Node;
import gamma.grammar.Nonterminal;
import gamma.grammar.Rule;
import gamma.grammar.SymbolNode;
import gamma.grammar.Terminal;
import gamma.input.earley.AffixForm;
import gamma.util.Position;
import io;
import log;
import std.range;
import std.typecons;
import symbols;

public class Parser
{
    private SymbolTable symbolTable;

    private Lexer lexer;

    private char token;

    private Position lastPosition;

    private Params spareActualParams;

    private Params undecidedActualParams;

    private GrammarBuilder metaGrammarBuilder;

    private GrammarBuilder hyperGrammarBuilder;

    private Nonterminal startSymbol;

    private bool[Nonterminal]lexicalMetaNonterminals;

    private bool[Nonterminal] lexicalHyperNonterminals;

    /**
     * Creates a parser for the given file.
     */
    public this(Input input)
    {

        this.symbolTable = new SymbolTable;
        this.lexer = Lexer(input, this.symbolTable);
    }

    private void markError(string message)
    {
        const position = this.lexer.position;

        if (position != this.lastPosition)
        {
            this.lexer.addError(position, message);
            this.lastPosition = position;
        }
    }

    /**
     * Specification:
     *     { WhiteSpaceRule | MetaRule | HyperRule }.
     *
     * The start symbol appears on the left-hand side of the first hyper rule.
     */
    public void parseSpecification()
    {
        for (;;)
        {
            if (this.lexer.front == ':')
            {
                parseWhiteSpaceRule;
            }
            else if (this.lexer.front == Token.name)
            {
                const value = this.lexer.value;
                const position = this.lexer.position;
                bool starred = false;

                this.lexer.popFront;
                if (this.lexer.front == Token.number)
                {
                    markError("unexpected number");
                    this.lexer.popFront;
                }
                if (this.lexer.front == '*')
                {
                    starred = true;
                    this.lexer.popFront;
                }
                if (this.lexer.front != '=' && this.lexer.front != ':' && this.lexer.front != '<')
                {
                    markError("unexpected symbol");
                    if (!this.lexer.empty && this.lexer.front != '.')
                        this.lexer.popFront;
                }
                if (this.lexer.front == '=')
                {
                    auto nonterminal = metaNonterminal(value);
                    auto lhs = new SymbolNode(nonterminal, position);

                    if (starred)
                        this.lexicalMetaNonterminals[nonterminal] = true;

                    parseMetaRule(lhs);
                }
                else if (this.lexer.front == ':' || this.lexer.front == '<')
                {
                    auto nonterminal = hyperNonterminal(value);
                    auto lhs = new HyperSymbolNode(nonterminal, null, position);  // TODO: which params?

                    if (starred)
                        this.lexicalHyperNonterminals[nonterminal] = true;
                    else
                        if (this.startSymbol is null)
                            this.startSymbol = nonterminal;

                    parseHyperRule(lhs);
                }
            }
            else if (this.lexer.empty)
                break;
            else
            {
                markError("start of some rule expected");
                // error recovery
                while (!this.lexer.empty && this.lexer.front != '.')
                {
                    trace!"skipping\n%s"(this.lexer.position);
                    this.lexer.popFront;
                }
                if (this.lexer.front == '.')
                    this.lexer.popFront;
            }
        }
    }

    /**
     * WhiteSpaceRule:
     *     ':' WhiteSpaceDefinition { '|' WhiteSpaceDefinition } '.'.
     */
    private void parseWhiteSpaceRule()
    in (this.lexer.front == ':')
    {
        this.lexer.popFront;

        for (;;)
        {
            if (this.lexer.front == Token.string_)
                parseWhiteSpaceDefinition;
            else
                markError("white space definition expected");
            if (!this.lexer.empty && this.lexer.front != '|' && this.lexer.front != '.')
            {
                markError("unexpected symbol");
                // error recovery
                do
                {
                    trace!"skipping\n%s"(this.lexer.position);
                    this.lexer.popFront;
                }
                while (!this.lexer.empty && this.lexer.front != '|' && this.lexer.front != '.');
            }
            if (this.lexer.front == '|')
                this.lexer.popFront;
            else
                break;
        }

        assert(this.lexer.empty || this.lexer.front == '.');

        if (this.lexer.front == '.')
            this.lexer.popFront;
        else
            markError(`"." expected`);
    }

    /**
     * WhiteSpaceDefinition:
     *     string                  ! white space
     *   | string '~'              ! comment that extends to end of line
     *   | string '~' string       ! comment in brackets
     *   | string '~' '~' string.  ! nesting comment in brackets
     */
    private void parseWhiteSpaceDefinition()
    in (this.lexer.front == Token.string_)
    {
        this.lexer.popFront;

        if (this.lexer.front == '~')
        {
            bool nestingComment = false;

            this.lexer.popFront;
            if (this.lexer.front == '~')
            {
                nestingComment = true;
                this.lexer.popFront;
            }
            if (this.lexer.front == Token.string_)
                this.lexer.popFront;
            else if (nestingComment)
                markError("closing bracket for nesting comment expected");
        }
    }

    /**
     * MetaRule:
     *     ident [ '*' ] '=' MetaExpr '.'.
     *
     * @param lhs  the identifier occurrence for the left-hand side
     */
    private void parseMetaRule(SymbolNode lhs)
    in (this.lexer.front == '=')
    {
        const position = this.lexer.position;

        this.lexer.popFront;
        parseMetaExpr(lhs, position);

        assert(this.lexer.empty || this.lexer.front == '.');

        if (this.lexer.front == '.')
            this.lexer.popFront;
        else
            markError(`"." expected`);
    }

    /**
     * MetaExpr:
     *     MetaTerm { '|' MetaTerm }.
     *
     * @param lhs       the identifier occurrence for the left-hand side
     * @param position  the position for the first alternative
     */
    private void parseMetaExpr(SymbolNode lhs, Position position)
    {
        for (;;)
        {
            Node[] rhs = parseMetaTerm;
            auto alternative = new Alternative(lhs, rhs, position);

            this.metaGrammarBuilder.add(alternative);

            assert(this.lexer.empty || this.lexer.front == '|' || this.lexer.front == '.');

            if (this.lexer.front != '|')
                break;
            position = this.lexer.position;
            this.lexer.popFront;
        }
    }

    /**
     * MetaTerm:
     *     { ident | string }.
     *
     * @return  the list of occurrences of identifiers and strings
     */
    private Node[] parseMetaTerm()
    {
        Node[] nodes;

        for (;;)
            if (this.lexer.front == Token.name)
            {
                nodes ~= new SymbolNode(metaNonterminal(this.lexer.value), this.lexer.position);
                this.lexer.popFront;
                if (this.lexer.front == Token.number)
                {
                    markError("unexpected number");
                    this.lexer.popFront;
                }
            }
            else if (this.lexer.front == Token.string_)
            {
                nodes ~= new SymbolNode(metaTerminal(this.lexer.value), this.lexer.position);
                this.lexer.popFront;
            }
            else if (this.lexer.empty || this.lexer.front == '|' || this.lexer.front == '.')
                break;
            else
            {
                markError("unexpected symbol");
                // error recovery
                do
                {
                    trace!"skipping\n%s"(this.lexer.position);
                    this.lexer.popFront;
                }
                while (!this.lexer.empty && this.lexer.front != '|' && this.lexer.front != '.');
            }

        return nodes;
    }

    /**
     * HyperRule:
     *     ident [ '*' ] [ FormalParams ] ':' HyperExpr '.'.
     *
     * @param lhs  the identifier occurrence for the left-hand side
     */
    private void parseHyperRule(HyperSymbolNode lhs)
    in (this.lexer.front == ':' || this.lexer.front == '<')
    {
        Position position;

        if (this.lexer.front == '<')
        {
            with (parseParams(Yes.formalParams))
            {
                // TODO: rewriting lhs requires cast to Nonterminal
                lhs = new HyperSymbolNode(cast(Nonterminal) lhs.symbol, params, lhs.position);
            }
        }
        if (this.lexer.front == ':')
        {
            position = this.lexer.position;
            this.lexer.popFront;
        } else
            markError(`":" expected`);

        Alternative[] alternatives = parseHyperExpr(lhs,
            No.repetition,
            position);

        foreach (alternative; alternatives)
            this.hyperGrammarBuilder.add(alternative);

        assert(this.lexer.empty || this.lexer.front == '.'
            || this.lexer.front == ')' || this.lexer.front == ']' || this.lexer.front == '}');

        if (this.lexer.front == '.')
            this.lexer.popFront;
        else
            markError(`"." expected`);
    }

    /**
     * HyperExpr:
     *     [ FormalParams ] HyperTerm [ ActualParams ]
     *     { '|' [ FormalParams ] HyperTerm [ ActualParams ] }.
     *
     * @param lhs  the identifier occurrence for the left-hand side
     * @return     the list of alternatives
     */
    private Alternative[] parseHyperExpr(HyperSymbolNode lhs,
        Flag!"repetition" repetition,
        Position position)
    {
        Alternative[] alternatives;
        Params formalParams = null;

        for (bool firstRound = true;; firstRound = false)
        {
            auto alternativeLhs = lhs;
            Params spareActualParams = null;

            if (this.lexer.front == '<')
            {
                with (parseParams)
                {
                    if (signature !is null)
                    {
                        if (lhs.params !is null || !firstRound && formalParams is null)
                        {
                            this.lexer.addError(params.position, "unexpected formal parameters");
                        }
                        else
                        {
                            // TODO: rewriting lhs requires cast to Nonterminal
                            alternativeLhs = new HyperSymbolNode(cast(Nonterminal) lhs.symbol, params, lhs.position);
                            formalParams = params;
                        }
                    }
                    else
                    {
                        if (formalParams !is null)
                            this.lexer.addError(params.position, "formal parameters expected");
                        else
                            spareActualParams = params;
                    }
                }
            }
            else if (formalParams !is null)
            {
                markError("formal parameters expected");
            }

            Node[] rhs = parseHyperTerm(spareActualParams);
            Alternative alternative;

            if (repetition)
                alternative = new RepetitionAlternative(alternativeLhs, rhs, null, position);  // TODO: which params?
            else
                alternative = new Alternative(alternativeLhs, rhs, position);
            alternatives ~= alternative;

            if (repetition && formalParams !is null)
            {
                if (this.undecidedActualParams is null && this.spareActualParams is null)
                    markError("actual parameters expected");
            }
            else
            {
                if (this.spareActualParams !is null)
                    this.lexer.addError(this.spareActualParams.position, "unexpected actual parameters");
            }

            assert(this.lexer.empty || this.lexer.front == '|' || this.lexer.front == '.'
                || this.lexer.front == ')' || this.lexer.front == ']' || this.lexer.front == '}');

            if (this.lexer.front != '|')
                break;
            position = this.lexer.position;
            this.lexer.popFront;
        }
        return alternatives;
    }

    /**
     * HyperTerm:
     *     { ident [ ActualParams ]
     *   | string
     *   | [ ActualParams ] ( '(' HyperExpr ')'
     *                      | '[' HyperExpr ']' [ FormalParams ]
     *                      | '{' HyperExpr '}' [ FormalParams ]
     *                      )
     *   }.
     *
     * @return  the list of occurrences of identifiers and strings
     */
    private Node[] parseHyperTerm(Params spareActualParams)
    {
        Node[] nodes;
        Params undecidedActualParams = null;

        for (;;)
        {
            if (this.lexer.front == Token.name || this.lexer.front == Token.string_ || this.lexer.front == '<')
            {
                undecidedActualParams = null;
                if (spareActualParams !is null)
                {
                    this.lexer.addError(spareActualParams.position, "unexpected actual parameters");
                    spareActualParams = null;
                }
                if (this.lexer.front == Token.name)
                {
                    auto nonterminal = hyperNonterminal(this.lexer.value);
                    const position = this.lexer.position;
                    auto node = new HyperSymbolNode(nonterminal, null, position);  // TODO: which params?

                    nodes ~= node;
                    this.lexer.popFront;
                    if (this.lexer.front == Token.number)
                    {
                        markError("unexpected number");
                        this.lexer.popFront;
                    }
                    if (this.lexer.front == '<')
                    {
                        with (parseParams(No.formalParams))
                        {
                            // formal parameters following a nonterminal
                            // can also belong to the next EBNF expression
                            undecidedActualParams = params;
                        }
                    }
                }
                else if (this.lexer.front == Token.string_)
                {
                    auto terminal = hyperTerminal(this.lexer.value);
                    auto node = new SymbolNode(terminal, this.lexer.position);

                    nodes ~= node;
                    this.lexer.popFront;
                }
                else if (this.lexer.front == '<')
                {
                    with (parseParams(No.formalParams))
                    {
                        spareActualParams = params;
                    }
                }
            }
            else if (this.lexer.front == '(' || this.lexer.front == '[' || this.lexer.front == '{')
            {
                const open = this.lexer.front;
                const position = this.lexer.position;

                this.lexer.popFront;

                Nonterminal identifier = hyperGrammarBuilder.buildAnonymousNonterminal;
                auto lhs = new HyperSymbolNode (identifier, null, position);  // TODO: which params?
                Alternative[] alternatives = parseHyperExpr(lhs,
                    (open == '{') ? Yes.repetition : No.repetition,
                    position);
                auto rule = new Rule(alternatives);
                Operator operator = null;

                assert(this.lexer.empty || this.lexer.front == '|' || this.lexer.front == '.'
                    || this.lexer.front == ')' || this.lexer.front == ']' || this.lexer.front == '}');

                if (open == '(')
                {
                    if (this.lexer.front != ')')
                        markError(`")" expected`);
                    operator = new Group(null, rule, position);
                }
                else if (open == '[')
                {
                    if (this.lexer.front != ']')
                        markError(`"]" expected`);
                    operator = new Option(null, rule, null, position);
                }
                else if (open == '{')
                {
                    if (this.lexer.front != '}')
                        markError(`"}" expected`);
                    operator = new Repetition(null, rule, null, position);
                }
                nodes ~= operator;

                if (this.lexer.front == ')' || this.lexer.front == ']' || this.lexer.front == '}')
                    this.lexer.popFront;
                if (open != '(' && (cast(HyperSymbolNode) rule.lhs).params !is null)
                {
                    if (this.lexer.front == '<')
                    {
                        parseParams(Yes.formalParams);
                    }
                    else
                        markError("formal parameters expected");
                }
                if ((cast(HyperSymbolNode) rule.lhs).params !is null)
                {
                    // FIXME: also OK for EBNF expression at beginning when LHS has no formal parameter
                    if (undecidedActualParams is null && spareActualParams is null && false)
                        this.lexer.addError(position, "actual parameters expected");
                }
                else
                {
                    if (spareActualParams !is null)
                        this.lexer.addError(spareActualParams.position, "unexpected actual parameters");
                }
                undecidedActualParams = null;
                spareActualParams = null;
            }
            else if (this.lexer.empty || this.lexer.front == '|' || this.lexer.front == '.'
                || this.lexer.front == ')' || this.lexer.front == ']' || this.lexer.front == '}')
            {
                break;
            }
            else
            {
                markError("unexpected symbol");
                // error recovery
                do
                {
                    trace!"skipping\n%s"(this.lexer.position);
                    this.lexer.popFront;
                }
                while (!this.lexer.empty && this.lexer.front != '|' && this.lexer.front != '.'
                    && this.lexer.front != '(' && this.lexer.front != '[' && this.lexer.front != '{');
            }
        }

        this.spareActualParams = spareActualParams;
        this.undecidedActualParams = undecidedActualParams;
        return nodes;
    }

    private auto parseParams(Flag!"formalParams" formalParams)
    {
        return parseParams(formalParams ? true.nullable : false.nullable);
    }

    /**
     * FormalParams:
     *     '<' ( '+' | '-' ) ( AffixForm ':' ident | Variable )
     *     { ',' ( '+' | '-' ) ( AffixForm ':' ident | Variable ) } '>'.
     * ActualParams:
     *     '<' AffixForm { ',' AffixForm } '>'.
     */
    private auto parseParams(Nullable!bool formalParams = Nullable!bool())
    in (this.lexer.front == '<')
    {
        import gamma.grammar.affixes.Direction : Direction;
        import gamma.grammar.affixes.Signature : Signature;

        Direction[] directions = null;
        Nonterminal[] domains = null;
        AffixForm[] affixForms = null;
        const position = this.lexer.position;

        this.lexer.popFront;
        for (;;)
        {
            Direction direction;

            if (this.lexer.front == '+' || this.lexer.front == '-')
            {
                direction = (this.lexer.front == '-') ? Direction.input : Direction.output;
                if (formalParams.isNull)
                    formalParams = true;
                if (!formalParams.get)
                    markError(`"+" or "-" unexpected for actual parameters`);
                this.lexer.popFront;
            }
            else
            {
                if (formalParams.isNull)
                    formalParams = false;
                if (formalParams.get)
                    markError(`"+" or "-" expected for formal parameters`);
            }

            AffixForm affixForm = parseAffixForm;

            affixForms ~= affixForm;
            if (formalParams.get)
            {
                if (this.lexer.front == ':')
                {
                    this.lexer.popFront;
                    if (this.lexer.front == Token.name)
                    {
                        auto nonterminal = metaNonterminal(this.lexer.value);

                        directions ~= direction;
                        domains ~= nonterminal;
                        this.lexer.popFront;
                        if (this.lexer.front == Token.number)
                        {
                            markError("unexpected number");
                            this.lexer.popFront;
                        }
                    }
                    else
                        markError("meta-nonterminal expected");
                }
                else if (affixForm.isSingleVariable)
                {
                    directions ~= direction;
                    domains ~= affixForm.variables.front.nonterminal;
                }
                else
                {
                    markError(`":" expected for formal parameters`);
                }
            }

            assert(directions.length == domains.length);

            if (!this.lexer.empty && this.lexer.front != '.'
                && this.lexer.front != ',' && this.lexer.front != '>')
            {
                markError("unexpected symbol");
                // error recovery
                do
                {
                    trace!"skipping\n%s"(this.lexer.position);
                    this.lexer.popFront;
                }
                while (!this.lexer.empty && this.lexer.front != '.'
                    && this.lexer.front != ',' && this.lexer.front != '>');
            }
            if (this.lexer.front == ',')
                this.lexer.popFront;
            else
                break;
        }
        if (this.lexer.front == '>')
            this.lexer.popFront;
        else
            markError(`">" expected`);

        Signature signature = null;
        auto params = new Params(affixForms, position);

        if (formalParams.get)
        {
            signature = new Signature(directions, domains, position);
        }
        return tuple!("signature", "params")(signature, params);
    }

    /**
     * AffixForm:
     *     { string | Variable }.
     * Variable:
     *     [ '!' ] ident [ number ].
     */
    private AffixForm parseAffixForm()
    {
        SymbolNode[] symbolNodes = null;
        Variable[] variables = null;

        for (;;)
        {
            if (this.lexer.front == Token.string_)
            {
                symbolNodes ~= new SymbolNode(metaTerminal(this.lexer.value), this.lexer.position);
                this.lexer.popFront;
            }
            else if (this.lexer.front == '!' || this.lexer.front == Token.name)
            {
                const position = this.lexer.position;
                bool unequal = false;

                if (this.lexer.front == '!')
                {
                    unequal = true;
                    this.lexer.popFront;
                }
                if (this.lexer.front == Token.name)
                {
                    auto nonterminal = metaNonterminal(this.lexer.value);

                    symbolNodes ~= new SymbolNode(nonterminal, this.lexer.position);
                    this.lexer.popFront;

                    const number = parseNumber;

                    variables ~= new Variable(unequal, nonterminal, number, position);
                }
                else
                {
                    markError("meta-variable expected");
                }
            }
            else
                break;
        }
        return new AffixForm(symbolNodes, variables);
    }

    private Nullable!int parseNumber()
    {
        import std.conv : ConvException, to;

        Nullable!int number;

        if (this.lexer.front == Token.number)
        {
            const representation = this.symbolTable.symbol(this.lexer.value);

            try
            {
                number = representation.to!int;
            }
            catch (ConvException)
            {
                markError("number out of range");
            }
            this.lexer.popFront;
        }
        return number;
    }

    private Nonterminal metaNonterminal(size_t value)
    {
        const representation = this.symbolTable.symbol(value);

        return this.metaGrammarBuilder.buildNonterminal(representation);
    }

    private Terminal metaTerminal(size_t value)
    {
        const representation = this.symbolTable.symbol(value);

        return this.metaGrammarBuilder.buildTerminal(representation);
    }

    private Nonterminal hyperNonterminal(size_t value)
    {
        const representation = this.symbolTable.symbol(value);

        return this.hyperGrammarBuilder.buildNonterminal(representation);
    }

    private Terminal hyperTerminal(size_t value)
    {
        const representation = this.symbolTable.symbol(value);

        return this.hyperGrammarBuilder.buildTerminal(representation);
    }

    public int getErrorCount() const
    {
        return this.lexer.ok ? 0 : 42; // FIXME
    }

    public Grammar yieldMetaGrammar()
    {
        if (this.lexer.ok && this.metaGrammarBuilder.grammarIsWellDefined)
        {
            return this.metaGrammarBuilder.getGrammar;
        }
        else
        {
            this.metaGrammarBuilder.markErrors;
            return null;
        }
    }

    public Grammar yieldHyperGrammar()
    {
        if (this.lexer.ok && this.startSymbol !is null && this.hyperGrammarBuilder.grammarIsWellDefined)
        {
            return this.hyperGrammarBuilder.getGrammar(this.startSymbol);
        }
        else
        {
            this.hyperGrammarBuilder.markErrors;
            return null;
        }
    }

    public bool[Nonterminal] getLexicalHyperNonterminals()
    {
        return lexicalHyperNonterminals;
    }
}

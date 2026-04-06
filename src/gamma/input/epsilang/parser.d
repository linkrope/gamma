module gamma.input.epsilang.parser;

import epsilon.lexer;
import gamma.grammar.affixes.Signature;
import gamma.grammar.affixes.Term;
import gamma.grammar.affixes.Variable;
import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.GrammarBuilder;
import gamma.grammar.hyper.Group;
import gamma.grammar.hyper.HyperGrammar;
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
    private static struct ParamsInfo
    {
        Params params;

        // null for actual params
        Signature signature;

        AffixForm[] affixForms;

        Term[] terms;
    }

    private SymbolTable symbolTable;

    private Lexer lexer;

    private char token;

    private Position lastPosition;

    private Params spareActualParams;

    private Params undecidedActualParams;

    private ParamsInfo[] paramsByKey;

    private GrammarBuilder metaGrammarBuilder;

    private Nullable!Grammar metaGrammar;

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

                    if (starred)
                        this.lexicalHyperNonterminals[nonterminal] = true;
                    else
                        if (this.startSymbol is null)
                            this.startSymbol = nonterminal;

                    parseHyperRule(nonterminal, position);

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
        parseAffixForms;
    }

    private void parseAffixForms()
    {
        import gamma.input.earley.Parser : Parser;

        auto metaGrammar = buildMetaGrammar;

        if (metaGrammar is null)
            return;

        auto parser = new Parser(metaGrammar);

        foreach (ref paramsInfo; this.paramsByKey) with (paramsInfo)
        {
            if (signature is null)
                continue;
            foreach (i, affixForm; affixForms)
            {
                auto term = parser.parse(signature.domains[i], affixForm);

                terms ~= term;
                if (term is null)
                    this.lexer.addError(params.position, "affix form does not match domain");
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
     */
    private void parseHyperRule(Nonterminal lhsNonterminal, Position lhsPosition)
    in (this.lexer.front == ':' || this.lexer.front == '<')
    {
        Params lhsParams = null;

        if (this.lexer.front == '<')
            lhsParams = parseParams(Yes.formalParams).params;

        Position position;

        if (this.lexer.front == ':')
        {
            position = this.lexer.position;
            this.lexer.popFront;
        } else
            markError(`":" expected`);

        Alternative[] alternatives = parseHyperExpr(lhsNonterminal, lhsParams, lhsPosition,
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
     */
    private Alternative[] parseHyperExpr(Nonterminal lhsNonterminal, Params lhsParams, Position lhsPosition,
        Flag!"repetition" repetition,
        Position position)
    {
        Alternative[] alternatives;
        Params formalParams = null;

        for (bool firstRound = true;; firstRound = false)
        {
            Params alternativeLhsParams = lhsParams;
            Params spareActualParams = null;

            if (this.lexer.front == '<')
            {
                with (parseParams)
                {
                    if (signature !is null)
                    {
                        if (lhsParams !is null || !firstRound && formalParams is null)
                        {
                            this.lexer.addError(params.position, "unexpected formal parameters");
                        }
                        else
                        {
                            alternativeLhsParams = params;
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

            auto alternativeLhs = new HyperSymbolNode(lhsNonterminal, alternativeLhsParams, lhsPosition);
            Node[] rhs = parseHyperTerm(spareActualParams);
            Alternative alternative;

            if (repetition)
            {
                Params params = (this.spareActualParams !is null) ? this.spareActualParams : this.undecidedActualParams;

                alternative = new RepetitionAlternative(alternativeLhs, rhs, params, position);
            }
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
                            // actual params following a nonterminal can also
                            // belong to the next EBNF expression (undecided)
                            undecidedActualParams = params;
                        }
                    }
                    // placeholder: the EBNF branch will claim it if hasFormalParams
                    nodes ~= new HyperSymbolNode(nonterminal, undecidedActualParams, position);
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
                Alternative[] alternatives = parseHyperExpr(identifier, null, position,
                    (open == '{') ? Yes.repetition : No.repetition,
                    position);
                auto rule = new Rule(alternatives);
                const hasFormalParams = (cast(HyperSymbolNode) rule.lhs).params !is null;
                Params params = (spareActualParams !is null)
                    ? spareActualParams
                    : hasFormalParams ? undecidedActualParams : null;

                // undo placeholder: undecidedActualParams belongs to the operator, not the preceding node
                if (hasFormalParams && undecidedActualParams !is null && !nodes.empty)
                {
                    auto node = cast(HyperSymbolNode) nodes.back;

                    if (node !is null && node.params is undecidedActualParams)
                        nodes.back = new HyperSymbolNode(cast(Nonterminal) node.symbol, null, node.position);
                }

                assert(this.lexer.empty || this.lexer.front == '|' || this.lexer.front == '.'
                    || this.lexer.front == ')' || this.lexer.front == ']' || this.lexer.front == '}');

                if (open == '(')
                {
                    if (this.lexer.front != ')')
                        markError(`")" expected`);
                }
                else if (open == '[')
                {
                    if (this.lexer.front != ']')
                        markError(`"]" expected`);
                }
                else if (open == '{')
                {
                    if (this.lexer.front != '}')
                        markError(`"}" expected`);
                }
                if (this.lexer.front == ')' || this.lexer.front == ']' || this.lexer.front == '}')
                    this.lexer.popFront;

                Params endParams = null;

                if ((open == '[' || open == '{') && hasFormalParams)
                {
                    if (this.lexer.front == '<')
                        endParams = parseParams(Yes.formalParams).params;
                    else
                        markError("formal parameters expected");
                }

                Operator operator;

                if (open == '(')
                    operator = new Group(params, rule, position);
                else if (open == '[')
                    operator = new Option(params, rule, endParams, position);
                else if (open == '{')
                    operator = new Repetition(params, rule, endParams, position);

                nodes ~= operator;
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

    private ParamsInfo parseParams(Flag!"formalParams" formalParams)
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
    private ParamsInfo parseParams(Nullable!bool formalParams = Nullable!bool())
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
        auto params = new Params(this.paramsByKey.length, position);

        if (formalParams.get)
        {
            signature = new Signature(directions, domains, position);
        }

        auto paramsInfo = ParamsInfo(params, signature, affixForms);

        this.paramsByKey ~= paramsInfo;
        return paramsInfo;
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

    public Grammar buildMetaGrammar()
    {
        if (this.metaGrammar.isNull)
        {
            Grammar grammar = this.lexer.ok ? this.metaGrammarBuilder.getGrammar : null;

            this.metaGrammar = grammar;
            if (grammar is null)
                this.metaGrammarBuilder.markErrors;
        }
        return this.metaGrammar.get;
    }

    public HyperGrammar buildHyperGrammar()
    {
        import std.algorithm : map;
        import std.array : array;

        if (this.lexer.ok && this.startSymbol !is null && this.hyperGrammarBuilder.grammarIsWellDefined)
        {
            Term[][] termsByKey = this.paramsByKey.map!"a.terms".array;
            Signature[] signaturesByKey = this.paramsByKey.map!"a.signature".array;

            return new HyperGrammar(this.hyperGrammarBuilder.getGrammar(this.startSymbol), termsByKey, signaturesByKey);
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

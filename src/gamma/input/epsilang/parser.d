module gamma.input.epsilang.parser;

import epsilon.lexer;
import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.GrammarBuilder;
import gamma.grammar.Node;
import gamma.grammar.Nonterminal;
import gamma.grammar.Rule;
import gamma.grammar.SymbolNode;
import gamma.grammar.Terminal;
import gamma.grammar.hyper.Group;
import gamma.grammar.hyper.HyperSymbolNode;
import gamma.grammar.hyper.Operator;
import gamma.grammar.hyper.Option;
import gamma.grammar.hyper.Repetition;
import gamma.grammar.hyper.RepetitionAlternative;
import gamma.util.Position;
import io;
import std.typecons;
import symbols;

public class Parser
{
    private SymbolTable symbolTable;

    private Lexer lexer;

    private char token;

    private Position lastPosition;

    private bool formalParams;

    private bool spareActualParams;

    private bool undecidedActualParams;

    private Position paramsPosition;

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
                const representation = this.symbolTable.symbol(this.lexer.value);
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
                    Nonterminal nonterminal = this.metaGrammarBuilder.buildNonterminal(representation);
                    SymbolNode lhs = new SymbolNode(nonterminal, position);

                    if (starred)
                        this.lexicalMetaNonterminals[nonterminal] = true;

                    parseMetaRule(lhs);
                }
                else if (this.lexer.front == ':' || this.lexer.front == '<')
                {
                    Nonterminal nonterminal = this.hyperGrammarBuilder.buildNonterminal(representation);
                    SymbolNode lhs = new HyperSymbolNode(nonterminal, null, position);

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
            {  // sync
                markError("start of some rule expected");
                while (!this.lexer.empty && this.lexer.front != '.')
                    this.lexer.popFront;
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
            {  // sync
                markError("unexpected symbol");
                do
                    this.lexer.popFront;
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
            markError(`symbol "." expected`);
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
            markError(`symbol "." expected`);
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
            Alternative alternative = new Alternative(lhs, rhs, position);

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
                const representation = this.symbolTable.symbol(this.lexer.value);
                Nonterminal nonterminal = this.metaGrammarBuilder.buildNonterminal(representation);
                const position = this.lexer.position;

                nodes ~= new SymbolNode(nonterminal, position);
                this.lexer.popFront;
                if (this.lexer.front == Token.number)
                {
                    markError("unexpected number");
                    this.lexer.popFront;
                }
            }
            else if (this.lexer.front == Token.string_)
            {
                const representation = this.symbolTable.symbol(this.lexer.value);
                Terminal terminal = this.metaGrammarBuilder.buildTerminal(representation);
                const position = this.lexer.position;

                nodes ~= new SymbolNode(terminal, position);
                this.lexer.popFront;
            }
            else if (this.lexer.empty || this.lexer.front == '|' || this.lexer.front == '.')
                break;
            else
            {  // sync
                markError("unexpected symbol");
                do
                    this.lexer.popFront;
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
    private void parseHyperRule(SymbolNode lhs)
    in (this.lexer.front == ':' || this.lexer.front == '<')
    {
        bool formalParams = false;
        Position position;

        if (this.lexer.front == '<')
        {
            this.lexer.popFront;
            parseFormalParams;
            formalParams = true;
        }
        if (this.lexer.front == ':')
        {
            position = this.lexer.position;
            this.lexer.popFront;
        } else
            markError(`symbol ":" expected`);

        Alternative[] alternatives = parseHyperExpr(lhs,
            formalParams ? No.formalParamsAllowed : Yes.formalParamsAllowed, No.repetition,
            position);

        foreach (alternative; alternatives)
            this.hyperGrammarBuilder.add(alternative);

        assert(this.lexer.empty || this.lexer.front == '.'
            || this.lexer.front == ')' || this.lexer.front == ']' || this.lexer.front == '}');

        if (this.lexer.front == '.')
            this.lexer.popFront;
        else
            markError(`symbol "." expected`);
    }

    /**
     * HyperExpr:
     *     [ FormalParams ] HyperTerm [ ActualParams ]
     *     { '|' [ FormalParams ] HyperTerm [ ActualParams ] }.
     *
     * @param lhs  the identifier occurrence for the left-hand side
     * @return     the list of alternatives
     */
    private Alternative[] parseHyperExpr(SymbolNode lhs,
        Flag!"formalParamsAllowed" formalParamsAllowed, Flag!"repetition" repetition,
        Position position)
    {
        Alternative[] alternatives;
        bool formalParams = false;

        for (bool firstRound = true;; firstRound = false)
        {
            bool spareActualParams = false;
            Position paramsPosition;

            if (this.lexer.front == '<')
            {
                paramsPosition = this.lexer.position;
                this.lexer.popFront;
                if (this.lexer.front == '+' || this.lexer.front == '-')
                {
                    parseFormalParams;
                    if (!formalParamsAllowed || !firstRound && !formalParams)
                        this.lexer.addError(paramsPosition, "unexpected formal parameters");
                    else
                        formalParams = true;
                }
                else
                {
                    parseActualParams;
                    if (formalParams)
                        this.lexer.addError(paramsPosition, "formal parameters expected");
                    else
                        spareActualParams = true;
                }
            }
            else if (formalParams)
                markError("formal parameters expected");

            Node[] rhs = parseHyperTerm(spareActualParams, paramsPosition);

            Alternative alternative;

            if (repetition)
                alternative = new RepetitionAlternative(lhs, rhs, null, position);
            else
                alternative = new Alternative(lhs, rhs, position);
            alternatives ~= alternative;

            if (repetition && formalParams)
            {
                if (!this.undecidedActualParams && !this.spareActualParams)
                    markError("actual parameters expected");
            }
            else
                if (this.spareActualParams)
                    this.lexer.addError(this.paramsPosition, "unexpected actual parameters");

            assert(this.lexer.empty || this.lexer.front == '|' || this.lexer.front == '.'
                || this.lexer.front == ')' || this.lexer.front == ']' || this.lexer.front == '}');

            if (this.lexer.front != '|')
                break;
            position = this.lexer.position;
            this.lexer.popFront;
        }

        this.formalParams = formalParams;
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
    private Node[] parseHyperTerm(bool spareActualParams, Position paramsPosition)
    {
        Node[] nodes;
        bool undecidedActualParams = false;

        for (;;)
        {
            if (this.lexer.front == Token.name || this.lexer.front == Token.string_ || this.lexer.front == '<')
            {
                undecidedActualParams = false;
                if (spareActualParams)
                {
                    this.lexer.addError(paramsPosition, "unexpected actual parameters");
                    spareActualParams = false;
                    paramsPosition = Position();
                }
                if (this.lexer.front == Token.name)
                {
                    const representation = this.symbolTable.symbol(this.lexer.value);
                    Nonterminal nonterminal = this.hyperGrammarBuilder.buildNonterminal(representation);
                    const position = this.lexer.position;
                    Node node = new HyperSymbolNode (nonterminal, null, position);

                    nodes ~= node;
                    this.lexer.popFront;
                    if (this.lexer.front == Token.number)
                    {
                        markError("unexpected number");
                        this.lexer.popFront;
                    }
                    if (this.lexer.front == '<')
                    {
                        this.lexer.popFront;
                        parseActualParams;
                        undecidedActualParams = true;
                    }
                }
                else if (this.lexer.front == Token.string_)
                {
                    const representation = this.symbolTable.symbol(this.lexer.value);
                    Terminal terminal = this.hyperGrammarBuilder.buildTerminal(representation);
                    const position = this.lexer.position;
                    Node node = new SymbolNode(terminal, position);

                    nodes ~= node;
                    this.lexer.popFront;
                }
                else if (this.lexer.front == '<')
                {
                    this.lexer.popFront;
                    parseActualParams;
                    spareActualParams = true;
                    paramsPosition = this.lexer.position;
                }
            }
            else if (this.lexer.front == '(' || this.lexer.front == '[' || this.lexer.front == '{')
            {
                const open = this.lexer.front;
                const position = this.lexer.position;

                this.lexer.popFront;

                Nonterminal identifier = hyperGrammarBuilder.buildAnonymousNonterminal;
                SymbolNode lhs = new HyperSymbolNode (identifier, null, position);
                Alternative[] alternatives = parseHyperExpr(lhs,
                    Yes.formalParamsAllowed, (open == '{') ? Yes.repetition : No.repetition,
                    position);
                Rule rule = new Rule(alternatives);
                Operator operator = null;

                assert(this.lexer.empty || this.lexer.front == '|' || this.lexer.front == '.'
                    || this.lexer.front == ')' || this.lexer.front == ']' || this.lexer.front == '}');

                if (open == '(')
                {
                    if (this.lexer.front != ')')
                        markError(`symbol ")" expected`);
                    operator = new Group(null, rule, position);
                }
                else if (open == '[')
                {
                    if (this.lexer.front != ']')
                        markError(`symbol "]" expected`);
                    operator = new Option(null, rule, null, position);
                }
                else if (open == '{')
                {
                    if (this.lexer.front != '}')
                        markError(`symbol "}" expected`);
                    operator = new Repetition(null, rule, null, position);
                }
                nodes ~= operator;

                if (this.lexer.front == ')' || this.lexer.front == ']' || this.lexer.front == '}')
                    this.lexer.popFront;
                if (open != '(' && this.formalParams)
                {
                    if (this.lexer.front == '<')
                    {
                        this.lexer.popFront;
                        parseFormalParams;
                    }
                    else
                        markError("formal parameters expected");
                }
                if (this.formalParams)
                {
                    // FIXME: also OK for EBNF expression at beginning when LHS has no formal parameter
                    if (!undecidedActualParams && !spareActualParams && false)
                        this.lexer.addError(position, "actual parameters expected");
                }
                else
                    if (spareActualParams)
                        this.lexer.addError(paramsPosition, "unexpected actual parameters");
                undecidedActualParams = false;
                spareActualParams = false;
                paramsPosition = Position();
            }
            else if (this.lexer.empty || this.lexer.front == '|' || this.lexer.front == '.'
                || this.lexer.front == ')' || this.lexer.front == ']' || this.lexer.front == '}')
                break;
            else
            {  // sync
                markError("unexpected symbol");
                do
                    this.lexer.popFront;
                while (!this.lexer.empty && this.lexer.front != '|' && this.lexer.front != '.'
                    && this.lexer.front != '(' && this.lexer.front != '[' && this.lexer.front != '{');
            }
        }

        this.spareActualParams = spareActualParams;
        this.undecidedActualParams = undecidedActualParams;
        this.paramsPosition = paramsPosition;
        return nodes;
    }

    /**
     * ActualParams:
     *     '<' AffixForm { ',' AffixForm } '>'.
     */
    private void parseActualParams()
    {
        for (;;)
        {
            if (this.lexer.front == '+' || this.lexer.front == '-')
            {
                markError(`symbol "+" or "-" not allowed in actual parameters`);
                this.lexer.popFront;
            }
            parseAffixForm;
            if (!this.lexer.empty && this.lexer.front != '.'
                && this.lexer.front != ',' && this.lexer.front != '>')
            {  // sync
                markError("unexpected symbol");
                do
                    this.lexer.popFront;
                while (!this.lexer.empty && this.lexer.front != '.'
                    && this.lexer.front != ',' && this.lexer.front != '>');
            }
            if (this.lexer.front == ',')
                this.lexer.popFront;
            else
                break;
        }

        assert(this.lexer.empty || this.lexer.front == '>' || this.lexer.front == '.');

        if (this.lexer.front == '>')
            this.lexer.popFront;
        else
            markError(`symbol ">" expected`);
    }

    /**
     * FormalParams:
     *     '<' ( '+' | '-' ) ( AffixForm ':' ident | Variable )
     *     { ',' ( '+' | '-' ) ( AffixForm ':' ident | Variable ) } '>'.
     */
    private void parseFormalParams()
    {
        for (;;)
        {
            if (this.lexer.front == '+' || this.lexer.front == '-')
            {
                this.lexer.popFront;
            }
            else
                markError(`symbol "+" or "-" expected`);

            const isVariable = parseAffixForm;

            if (this.lexer.front == ':')
            {
                this.lexer.popFront;
                if (this.lexer.front == Token.name)
                {
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
            else if (!isVariable)
                markError(`symbol ":" expected`);
            if (!this.lexer.empty && this.lexer.front != '.'
                && this.lexer.front != ',' && this.lexer.front != '>')
            {  // sync
                markError("unexpected symbol");
                do
                    this.lexer.popFront;
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
            markError(`symbol ">" expected`);
    }

    /**
     * AffixForm:
     *     { string | Variable }.
     */
    private bool parseAffixForm()
    {
        bool isVariable = false;

        for (bool firstRound = true;; firstRound = false)
        {
            if (this.lexer.front == Token.string_)
            {
                this.lexer.popFront;
                isVariable = false;
            }
            else if (this.lexer.front == '!' || this.lexer.front == Token.name)
            {
                parseVariable;
                isVariable = firstRound;
            }
            else
                break;
        }
        return isVariable;
    }

    /**
     * Variable:
     *     [ '!' ] ident [ number ].
     */
    private void parseVariable()
    in (this.lexer.front == '!' || this.lexer.front == Token.name)
    {
        if (this.lexer.front == '!')
            this.lexer.popFront;
        if (this.lexer.front == Token.name)
        {
            this.lexer.popFront;
            if (this.lexer.front == Token.number)
                this.lexer.popFront;
        }
        else
            markError("meta-variable expected");
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

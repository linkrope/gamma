module gamma.input.epsilang.Analyzer;

import gamma.input.epsilang.Scanner;
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
import std.stdio;
import std.typecons;

public class Analyzer
{
    private Scanner scanner;

    private char token;

    private Position lastPosition = null;

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
     * Creates an analyzer for the given file.
     */
    public this(File input)
    {
        this.scanner = new Scanner(input);
        this.token = this.scanner.read;
    }

    private void markError(string message)
    {
        Position position = this.scanner.getPosition;

        if (position != this.lastPosition)
        {
            position.markError(message);
            this.lastPosition = position;
        }
    }

    /**
     * Specification:
     *     { WhiteSpaceRule | MetaRule | HyperRule }.
     */
    public void parseSpecification()
    {
        for (;;)
        {
            if (this.token == ':')
            {
                parseWhiteSpaceRule;
            }
            else if (this.token == Scanner.SYNTACTIC_VARIABLE || this.token == Scanner.LEXICAL_VARIABLE)
            {
                const representation = this.scanner.getRepresentation;
                Position position = this.scanner.getPosition;
                const variableToken = this.token;

                this.token = this.scanner.read;
                if (this.token == Scanner.NUMBER)
                {
                    markError("unexpected number");
                    this.token = this.scanner.read;
                }
                if (this.token != '=' && this.token != ':' && this.token != '<')
                {
                    markError("unexpected symbol");
                    if (this.token != '.' && this.token != Scanner.END)
                        this.token = this.scanner.read;
                }
                if (this.token == '=')
                {
                    Nonterminal nonterminal = this.metaGrammarBuilder.buildNonterminal(representation);
                    SymbolNode lhs = new SymbolNode(nonterminal, position);

                    if (variableToken == Scanner.LEXICAL_VARIABLE)
                        this.lexicalMetaNonterminals[nonterminal] = true;

                    parseMetaRule(lhs);
                }
                else if (this.token == ':' || this.token == '<')
                {
                    Nonterminal nonterminal = this.hyperGrammarBuilder.buildNonterminal(representation);
                    SymbolNode lhs = new HyperSymbolNode(nonterminal, null, position);

                    if (variableToken == Scanner.LEXICAL_VARIABLE)
                        this.lexicalHyperNonterminals[nonterminal] = true;

                    if ( variableToken == Scanner.SYNTACTIC_VARIABLE )
                        this.startSymbol = nonterminal;

                    parseHyperRule(lhs);
                }
            }
            else if (this.token == Scanner.END)
                break;
            else
            {  // sync
                markError("start of some rule expected");
                while (this.token != '.' && this.token != Scanner.END)
                    this.token = this.scanner.read;
                if (this.token == '.')
                    this.token = this.scanner.read;
            }
        }
    }

    /**
     * WhiteSpaceRule:
     *     ":" WhiteSpaceDefinition { "|" WhiteSpaceDefinition } ".".
     */
    private void parseWhiteSpaceRule()
    in (this.token == ':')
    {
        this.token = this.scanner.read;

        for (;;)
        {
            if (this.token == Scanner.LITERAL)
                parseWhiteSpaceDefinition;
            else
                markError("white space definition expected");
            if (this.token != '|' && this.token != '.' && this.token != Scanner.END)
            {  // sync
                markError("unexpected symbol");
                do
                    this.token = this.scanner.read;
                while (this.token != '|' && this.token != '.' && this.token != Scanner.END);
            }
            if (this.token == '|')
                this.token = this.scanner.read;
            else
                break;
        }

        assert(this.token == '.' || this.token == Scanner.END);

        if (this.token == '.')
            this.token = this.scanner.read;
        else
            markError("symbol \".\" expected");
    }

    /**
     * WhiteSpaceDefinition:
     *     string                  ! white space
     *   | string "~"              ! comment that extends to end of line
     *   | string "~" string       ! comment in brackets
     *   | string "~" "~" string.  ! nesting comment in brackets
     */
    private void parseWhiteSpaceDefinition()
    in (this.token == Scanner.LITERAL)
    {
        this.token = this.scanner.read;

        if (this.token == '~')
        {
            bool nestingComment = false;

            this.token = this.scanner.read;
            if (this.token == '~')
            {
                nestingComment = true;
                this.token = this.scanner.read;
            }
            if (this.token == Scanner.LITERAL)
                this.token = this.scanner.read;
            else if (nestingComment)
                markError("closing bracket for nesting comment expected");
        }
    }

    /**
     * MetaRule:
     *     ident "=" MetaExpr ".".
     *
     * @param lhs  the identifier occurrence for the left-hand side
     */
    private void parseMetaRule(SymbolNode lhs)
    in (this.token == '=')
    {
        Position position = this.scanner.getPosition();

        this.token = this.scanner.read;
        parseMetaExpr(lhs, position);

        assert(this.token == '.' || this.token == Scanner.END);

        if (this.token == '.')
            this.token = this.scanner.read;
        else
            markError("symbol \".\" expected");
    }

    /**
     * MetaExpr:
     *     MetaTerm { "|" MetaTerm }.
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

            assert(this.token == '|' || this.token == '.' || this.token == Scanner.END);

            if (this.token != '|')
                break;
            position = this.scanner.getPosition;
            this.token = this.scanner.read;
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
            if (this.token == Scanner.SYNTACTIC_VARIABLE || this.token == Scanner.LEXICAL_VARIABLE)
            {
                const representation = this.scanner.getRepresentation;
                Nonterminal nonterminal = this.metaGrammarBuilder.buildNonterminal(representation);
                Position position = this.scanner.getPosition;

                nodes ~= new SymbolNode(nonterminal, position);
                this.token = this.scanner.read;
                if (this.token == Scanner.NUMBER)
                {
                    markError("unexpected number");
                    this.token = this.scanner.read;
                }
            }
            else if (this.token == Scanner.LITERAL)
            {
                const representation = this.scanner.getRepresentation;
                Terminal terminal = this.metaGrammarBuilder.buildTerminal(representation);
                Position position = this.scanner.getPosition;

                nodes ~= new SymbolNode(terminal, position);
                this.token = this.scanner.read;
            }
            else if (this.token == '|' || this.token == '.' || this.token == Scanner.END)
                break;
            else
            {  // sync
                markError("unexpected symbol");
                do
                    this.token = this.scanner.read;
                while (this.token != '|' && this.token != '.' && this.token != Scanner.END);
            }

        return nodes;
    }

    /**
     * HyperRule:
     *     ident [ FormalParams ] ":" HyperExpr ".".
     *
     * @param lhs  the identifier occurrence for the left-hand side
     */
    private void parseHyperRule(SymbolNode lhs)
    in (this.token == ':' || this.token == '<')
    {
        bool formalParams = false;
        Position position = null;

        if (this.token == '<')
        {
            this.token = this.scanner.read;
            parseFormalParams;
            formalParams = true;
        }
        if (this.token == ':')
        {
            position = this.scanner.getPosition;
            this.token = this.scanner.read;
        } else
            markError("symbol \":\" expected");

        Alternative[] alternatives = parseHyperExpr(lhs,
            formalParams ? No.formalParamsAllowed : Yes.formalParamsAllowed, No.repetition,
            position);

        foreach (alternative; alternatives)
            this.hyperGrammarBuilder.add(alternative);

        assert(this.token == ')' || this.token == ']' || this.token == '}'
            || this.token == '.' || this.token == Scanner.END);

        if (this.token == '.')
            this.token = this.scanner.read;
        else
            markError("symbol \".\" expected");
    }

    /**
     * HyperExpr:
     *     [ FormalParams ] HyperTerm [ ActualParams ]
     *     { "|" [ FormalParams ] HyperTerm [ ActualParams ] }.
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
            Position paramsPosition = null;

            if (this.token == '<')
            {
                paramsPosition = this.scanner.getPosition;
                this.token = this.scanner.read;
                if (this.token == '+' || this.token == '-')
                {
                    parseFormalParams;
                    if (!formalParamsAllowed || !firstRound && !formalParams)
                        paramsPosition.
                            markError("unexpected formal parameters");
                    else
                        formalParams = true;
                }
                else
                {
                    parseActualParams;
                    if (formalParams)
                        paramsPosition.
                            markError("formal parameters expected");
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
                    this.paramsPosition.markError("unexpected actual parameters");

            assert(this.token == ')' || this.token == ']' || this.token == '}'
                || this.token == '|' || this.token == '.' || this.token == Scanner.END);

            if (this.token != '|')
                break;
            position = this.scanner.getPosition;
            this.token = this.scanner.read;
        }

        this.formalParams = formalParams;
        return alternatives;
    }

    /**
     * HyperTerm:
     *     { ident [ ActualParams ]
     *   | string
     *   | [ ActualParams ] ( "(" HyperExpr ")"
     *                      | "[" HyperExpr "]" [ FormalParams ]
     *                      | "{" HyperExpr "}" [ FormalParams ]
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
            if (this.token == Scanner.SYNTACTIC_VARIABLE || this.token == Scanner.LEXICAL_VARIABLE
                || this.token == Scanner.LITERAL || this.token == '<')
            {
                undecidedActualParams = false;
                if (spareActualParams)
                {
                    paramsPosition.markError("unexpected actual parameters");
                    spareActualParams = false;
                    paramsPosition = null;
                }
                if (this.token == Scanner.SYNTACTIC_VARIABLE || this.token == Scanner.LEXICAL_VARIABLE)
                {
                    const representation = this.scanner.getRepresentation;
                    Nonterminal nonterminal = this.hyperGrammarBuilder.buildNonterminal(representation);
                    Position position = this.scanner.getPosition;
                    Node node = new HyperSymbolNode (nonterminal, null, position);

                    nodes ~= node;
                    this.token = this.scanner.read;
                    if (this.token == Scanner.NUMBER)
                    {
                        markError("unexpected number");
                        this.token = this.scanner.read;
                    }
                    if (this.token == '<')
                    {
                        this.token = this.scanner.read;
                        parseActualParams;
                        undecidedActualParams = true;
                    }
                }
                else if (this.token == Scanner.LITERAL)
                {
                    const representation = this.scanner.getRepresentation;
                    Terminal terminal = this.hyperGrammarBuilder.buildTerminal(representation);
                    Position position = this.scanner.getPosition;
                    Node node = new SymbolNode(terminal, position);

                    nodes ~= node;
                    this.token = this.scanner.read;
                }
                else if (this.token == '<')
                {
                    this.token = this.scanner.read;
                    parseActualParams;
                    spareActualParams = true;
                    paramsPosition = this.scanner.getPosition;
                }
            }
            else if (this.token == '(' || this.token == '[' || this.token == '{')
            {
                const open = this.token;
                Position position = this.scanner.getPosition;

                this.token = this.scanner.read;

                Nonterminal identifier = hyperGrammarBuilder.buildGeneratedNonterminal;
                SymbolNode lhs = new HyperSymbolNode (identifier, null, position);
                Alternative[] alternatives = parseHyperExpr(lhs,
                    Yes.formalParamsAllowed, (open == '{') ? Yes.repetition : No.repetition,
                    position);
                Rule rule = new Rule(alternatives);
                Operator operator = null;

                assert(this.token == ')' || this.token == ']' || this.token == '}'
                    || this.token == '|' || this.token == '.' || this.token == Scanner.END);

                if (open == '(')
                {
                    if (this.token != ')')
                        markError("symbol \")\" expected");
                    operator = new Group(null, rule, position);
                }
                else if (open == '[')
                {
                    if (this.token != ']')
                        markError("symbol \"]\" expected");
                    operator = new Option(null, rule, null, position);
                }
                else if (open == '{')
                {
                    if (this.token != '}')
                        markError("symbol \"}\" expected");
                    operator = new Repetition(null, rule, null, position);
                }
                nodes ~= operator;

                if (this.token == ')' || this.token == ']' || this.token == '}')
                    this.token = this.scanner.read;
                if (open != '(' && this.formalParams)
                {
                    if (this.token == '<')
                    {
                        this.token = this.scanner.read;
                        parseFormalParams;
                    }
                    else
                        markError("formal parameters expected");
                }
                if (this.formalParams)
                {
                    if (!undecidedActualParams && !spareActualParams)
                        position.markError("actual parameters expected");
                }
                else
                    if (spareActualParams)
                        paramsPosition.markError("unexpected actual parameters");
                undecidedActualParams = false;
                spareActualParams = false;
                paramsPosition = null;
            }
            else if (this.token == ')' || this.token == ']' || this.token == '}'
                || this.token == '|' || this.token == '.' || this.token == Scanner.END)
                break;
            else
            {  // sync
                markError("unexpected symbol");
                do
                    this.token = this.scanner.read;
                while (this.token != '(' && this.token != '[' && this.token != '{'
                    && this.token != '|' && this.token != '.' && this.token != Scanner.END);
            }
        }

        this.spareActualParams = spareActualParams;
        this.undecidedActualParams = undecidedActualParams;
        this.paramsPosition = paramsPosition;
        return nodes;
    }

    /**
     * ActualParams:
     *     "<" AffixForm { "," AffixForm } ">".
     */
    private void parseActualParams()
    {
        for (;;)
        {
            if (this.token == '+' || this.token == '-')
            {
                markError("symbol \"+\" or \"-\" not allowed in actual parameters");
                this.token = this.scanner.read;
            }
            parseAffixForm;
            if (this.token != ',' && this.token != '>'
                && this.token != '.' && this.token != Scanner.END)
            {  // sync
                markError("unexpected symbol");
                do
                    this.token = this.scanner.read;
                while (this.token != ',' && this.token != '>'
                    && this.token != '.' && this.token != Scanner.END);
            }
            if (this.token == ',')
                this.token = this.scanner.read;
            else
                break;
        }

        assert(this.token == '>' || this.token == '.' || this.token == Scanner.END);

        if (this.token == '>')
            this.token = this.scanner.read;
        else
            markError("symbol \">\" expected");
    }

    /**
     * FormalParams:
     *     "<" ( "+" | "-" ) ( AffixForm ":" ident | Variable )
     *     { "," ( "+" | "-" ) ( AffixForm ":" ident | Variable ) } ">".
     */
    private void parseFormalParams()
    {
        for (;;)
        {
            if (this.token == '+' || this.token == '-')
            {
                this.token = this.scanner.read;
            }
            else
                markError("symbol \"+\" or \"-\" expected");

            const isVariable = parseAffixForm;

            if (this.token == ':')
            {
                this.token = this.scanner.read;
                if (this.token == Scanner.SYNTACTIC_VARIABLE || this.token == Scanner.LEXICAL_VARIABLE)
                {
                    this.token = this.scanner.read;
                    if (this.token == Scanner.NUMBER)
                    {
                        markError("unexpected number");
                        this.token = this.scanner.read;
                    }
                }
                else
                    markError("meta-nonterminal expected");
            }
            else if (!isVariable)
                markError("symbol \":\" expected");
            if (this.token != ',' && this.token != '>'
                && this.token != '.' && this.token != Scanner.END)
            {  // sync
                markError("unexpected symbol");
                do
                    this.token = this.scanner.read;
                while (this.token != ',' && this.token != '>'
                    && this.token != '.' && this.token != Scanner.END);
            }
            if (this.token == ',')
                this.token = this.scanner.read;
            else
                break;
        }
        if (this.token == '>')
            this.token = this.scanner.read;
        else
            markError("symbol \">\" expected");
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
            if (this.token == Scanner.LITERAL)
            {
                this.token = this.scanner.read;
                isVariable = false;
            }
            else if (this.token == '#'
                || this.token == Scanner.SYNTACTIC_VARIABLE || this.token == Scanner.LEXICAL_VARIABLE)
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
     *     [ "#" ] ident [ number ].
     */
    private void parseVariable()
    in (this.token == '#'
        || this.token == Scanner.SYNTACTIC_VARIABLE || this.token == Scanner.LEXICAL_VARIABLE)
    {
        if (this.token == '#')
            this.token = this.scanner.read;
        if (this.token == Scanner.SYNTACTIC_VARIABLE || this.token == Scanner.LEXICAL_VARIABLE)
        {
            this.token = this.scanner.read;
            if (this.token == Scanner.NUMBER)
                this.token = this.scanner.read;
        }
        else
            markError("meta-variable expected");
    }

    public int getErrorCount() const
    {
        return this.scanner.getErrorCount;
    }

    public Grammar yieldHyperGrammar()
    {
        if (this.scanner.getErrorCount == 0 && this.startSymbol !is null
            && this.hyperGrammarBuilder.grammarIsWellDefined)
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

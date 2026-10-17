module gamma.grammar.hyper.HyperGrammar;

import gamma.grammar.affixes.Composite;
import gamma.grammar.affixes.Direction;
import gamma.grammar.affixes.Signature;
import gamma.grammar.affixes.Term;
import gamma.grammar.affixes.Variable;
import gamma.grammar.Alternative;
import gamma.grammar.Grammar;
import gamma.grammar.hyper.AnonymousNonterminal;
import gamma.grammar.hyper.HyperLhsNode;
import gamma.grammar.hyper.HyperSymbolNode;
import gamma.grammar.hyper.Operator;
import gamma.grammar.hyper.Option;
import gamma.grammar.hyper.Params;
import gamma.grammar.hyper.Repetition;
import gamma.grammar.hyper.RepetitionAlternative;
import gamma.grammar.Nonterminal;
import gamma.grammar.Rule;
import gamma.util.Position;
import log : error;
import std.range;

/**
 * Validates a grammar and bundles it with its affix trees.
 * Returns null after reporting grammar errors.
 */
public HyperGrammar buildHyperGrammar(Grammar grammar, Term[][] terms)
{
    with (SignatureCollector())
    {
        collect(grammar);
        if (!valid)
            return null;

        auto hyperGrammar = new HyperGrammar(grammar, terms, signatures);
        auto checkGrammar = hyperGrammar.plainHyperGrammar.grammar;

        if (!checkGrammar.hasValidAffixVariables(terms, signatures))
            return null;

        return hyperGrammar;
    }

}

/**
 * Bundles a hyper grammar with its affix trees.
 * Affix trees are referenced indirectly via a key stored in each Params.
 */
class HyperGrammar
{
    alias grammar this;

    private Grammar grammar_;

    private Term[][] terms_;

    private HyperGrammar plainHyperGrammar_;

    private Signature[Nonterminal] signatures;

    private this(Grammar grammar, Term[][] terms, Signature[Nonterminal] signatures)
    {
        this.grammar_ = grammar;
        this.terms_ = terms;
        this.signatures = signatures;
    }

    public Grammar grammar()
    {
        return this.grammar_;
    }

    /**
     * Returns the plain hyper grammar, converting and caching it on first access.
     */
    public HyperGrammar plainHyperGrammar()
    {
        import gamma.grammar.hyper.EBNFConverter : convert;

        if (this.grammar_.isPlain)
            return this;
        if (this.plainHyperGrammar_ is null)
            this.plainHyperGrammar_ = new HyperGrammar(this.grammar_.convert, this.terms_, this.signatures);

        return this.plainHyperGrammar_;
    }

    public Signature signatureOf(Nonterminal nonterminal)
    {
        return this.signatures.get(nonterminal, null);
    }

    public Term[][] terms()
    {
        return this.terms_;
    }

    public Term[] terms(size_t key)
    in (key < this.terms_.length)
    {
        return this.terms_[key];
    }
}

private struct SignatureCollector
{
    Signature[Nonterminal] signatures;

    bool valid = true;

    bool[Rule] visited;

    bool[Rule] checkedReferences;

    Position[Nonterminal] positions;

    void collect(Grammar grammar)
    {
        import std.algorithm : each;

        grammar.rules.each!(rule => collect(rule));
        if (this.valid)
            grammar.rules.each!(rule => checkReferences(rule));
    }

    void collect(Rule rule)
    {
        if (rule in this.visited)
            return;

        this.visited[rule] = true;

        auto direct = rule.directOperator;

        foreach (alternative; rule.alternatives)
        {
            auto lhs = cast(HyperLhsNode) alternative.lhs;
            Signature signature = (lhs is null) ? null : lhs.signature;

            // A direct operator supplies the otherwise omitted outer signature.
            if (direct !is null)
            {
                auto innerLhs = cast(HyperLhsNode) direct.rule.lhs;

                signature = (innerLhs is null) ? null : innerLhs.signature;
            }
            this.record(alternative.lhs.nonterminal, signature, alternative.lhs.position);

            foreach (node; alternative.rhs)
                if (auto operator = cast(Operator) node)
                    this.collect(operator.rule);
        }
    }

    void checkReferences(Rule rule)
    {
        if (rule in this.checkedReferences)
            return;

        this.checkedReferences[rule] = true;

        auto direct = cast(AnonymousNonterminal) rule.lhs.nonterminal ? null : rule.directOperator;

        foreach (alternative; rule.alternatives)
            foreach (node; alternative.rhs)
            {
                if (auto symbol = cast(HyperSymbolNode) node)
                {
                    auto nonterminal = cast(Nonterminal) symbol.symbol;
                    auto signature = this.signatures.get(nonterminal, null);

                    if (symbol.params is null && signature !is null && !signature.isEmpty)
                    {
                        error!"missing actual parameters for %s\n%s"(nonterminal, symbol.position);
                        this.valid = false;
                    }
                }
                else if (auto operator = cast(Operator) node)
                {
                    auto signature = this.signatures.get(operator.rule.lhs.nonterminal, null);

                    if (operator !is direct && operator.params is null && signature !is null && !signature.isEmpty)
                    {
                        error!"missing actual parameters for EBNF expression\n%s"(operator.position);
                        this.valid = false;
                    }
                    this.checkReferences(operator.rule);
                }
            }
    }

    void record(Nonterminal nonterminal, Signature signature, Position position)
    {
        if (auto existing = nonterminal in this.signatures)
        {
            bool equal;

            if (*existing is null)
                equal = signature is null || signature.isEmpty;
            else if (signature is null)
                equal = (*existing).isEmpty;
            else
                equal = *existing == signature;

            if (!equal)
            {
                error!"formal params for %s differ\n%s\n%s"(nonterminal, this.positions[nonterminal],
                    (signature is null) ? position : signature.position);
                this.valid = false;
            }
        }
        else
        {
            this.signatures[nonterminal] = signature;
            this.positions[nonterminal] = (signature is null) ? position : signature.position;
        }
    }
}

private bool hasValidAffixVariables(Grammar grammar, Term[][] terms, Signature[Nonterminal] signatures)
{
    import std.algorithm : each;

    with (AffixVariableChecker(terms, signatures))
    {
        grammar.rules.each!(rule => check(rule));
        return valid;
    }
}

private struct AffixVariableChecker
{
    private Term[][] terms;

    private Signature[Nonterminal] signatures;

    private bool[Rule] checkedRules;

    bool valid = true;

    this(Term[][] terms, Signature[Nonterminal] signatures)
    {
        this.terms = terms;
        this.signatures = signatures;
    }

    void check(Rule rule)
    {
        import std.algorithm : each;

        if (rule in this.checkedRules)
            return;

        this.checkedRules[rule] = true;

        rule.alternatives.each!(alternative => check(alternative));
    }

    private void check(Alternative alternative)
    {
        VariableUse[] variables;
        auto lhs = cast(HyperLhsNode) alternative.lhs;
        auto signature = this.signatures.get(alternative.lhs.nonterminal, null);

        if (lhs !is null)
            collect(lhs.params, signature, isLhs: true, variables);

        if (auto repetitionAlternative = cast(RepetitionAlternative) alternative)
            collectRepetitionActual(repetitionAlternative, signature, variables);

        foreach (node; alternative.rhs)
        {
            if (auto symbol = cast(HyperSymbolNode) node)
            {
                auto nonterminal = cast(Nonterminal) symbol.symbol;

                collect(symbol.params, this.signatures.get(nonterminal, null), isLhs: false, variables);
            }
            else if (auto operator = cast(Operator) node)
            {
                auto operatorSignature =
                    this.signatures.get(operator.rule.lhs.nonterminal, null);

                collect(operator.params, operatorSignature, isLhs: false, variables);
                checkEndParams(operator, operatorSignature);
                check(operator.rule);
            }
        }
        check(variables);
    }

    private void collectRepetitionActual(RepetitionAlternative alternative, Signature signature,
        ref VariableUse[] variables)
    {
        if (alternative.params is null)
            return;

        if (!alternative.rhs.empty)
            if (auto symbol = cast(HyperSymbolNode) alternative.rhs.back)
                if (symbol.params !is null && symbol.params.key == alternative.params.key)
                    return;

        collect(alternative.params, signature, isLhs: false, variables);
    }

    private void checkEndParams(Operator operator, Signature signature)
    {
        Params params;

        if (auto option = cast(Option) operator)
            params = option.endParams;
        else if (auto repetition = cast(Repetition) operator)
            params = repetition.endParams;

        if (params is null)
            return;

        VariableUse[] variables;

        collect(params, signature, isLhs: true, variables);
        check(variables);
    }

    private void collect(Params params, Signature signature, bool isLhs, ref VariableUse[] variables)
    {
        if (params is null || signature is null)
            return;

        foreach (index, term; this.terms[params.key])
        {
            if (index >= signature.length)
                break;
            collect(term, isLhs, signature.direction[index], variables);
        }
    }

    private void collect(Term term, bool isLhs, Direction direction, ref VariableUse[] variables)
    {
        if (auto variable = cast(Variable) term)
        {
            const isDef = isLhs ? direction == Direction.input : direction == Direction.output;

            variables ~= VariableUse(variable, isDef);
        }
        else if (auto composite = cast(Composite) term)
        {
            foreach (child; composite.terms)
                collect(child, isLhs, direction, variables);
        }
    }

    private void check(VariableUse[] variables)
    {
        foreach (index, use; variables)
        {
            if (!isFirstUse(index, variables))
                continue;

            if (use.variable.unequal && !hasPositivePartner(use.variable, variables))
                this.reportUndefinedVariable(use.variable.toString[1 .. $], use.variable.position);
            if (!hasDefiningUse(use.variable, variables))
                this.reportUndefinedVariable(use.variable.toString, use.variable.position);
        }
    }

    private void reportUndefinedVariable(string variable, Position position)
    {
        error!"variable %s never on defining position\n%s"(variable, position);
        this.valid = false;
    }
}

private struct VariableUse
{
    Variable variable;

    bool isDef;
}

private bool hasPositivePartner(Variable variable, VariableUse[] variables)
{
    foreach (use; variables)
        if (!use.variable.unequal && use.variable.matchesName(variable))
            return true;
    return false;
}

private bool hasDefiningUse(Variable variable, VariableUse[] variables)
{
    foreach (use; variables)
        if (use.isDef && use.variable == variable)
            return true;
    return false;
}

private bool isFirstUse(size_t index, VariableUse[] variables)
{
    foreach (previous; variables[0 .. index])
        if (previous.variable == variables[index].variable)
            return false;
    return true;
}


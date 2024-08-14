module gamma.grammar.hyper.Params;

import gamma.input.earley.AffixForm;
import gamma.util.Position;

// FXIME: gamma.grammar max not depend on gamma.input.earley
public class Params
{
    private AffixForm[] affixForms_;

    private Position position_;

    public this(AffixForm[] affixForms, Position position)
    {
        this.affixForms_ = affixForms;
        this.position_ = position;
    }

    public AffixForm[] affixForms()
    {
        return this.affixForms_;
    }

    public Position position()
    {
        return this.position_;
    }
}

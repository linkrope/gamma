module gamma.grammar.hyper.HyperVisitor;

import gamma.grammar.hyper.ActualParams;
import gamma.grammar.hyper.Group;
import gamma.grammar.hyper.HyperAlternative;
import gamma.grammar.hyper.Option;
import gamma.grammar.hyper.Repetition;
import gamma.grammar.Visitor;

public interface HyperVisitor : Visitor
{
    public void visit(HyperAlternative);

    public void visit(ActualParams);

    public void visit(Group);

    public void visit(Option);

    public void visit(Repetition);
}

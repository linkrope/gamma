module gamma.grammar.hyper.HyperVisitor;

import gamma.grammar.hyper.Group;
import gamma.grammar.hyper.Option;
import gamma.grammar.hyper.Repetition;
import gamma.grammar.hyper.RepetitionAlternative;
import gamma.grammar.Visitor;

public interface HyperVisitor : Visitor
{
    public void visit(Group group);

    public void visit(Option option);

    public void visit(Repetition repetition);

    public void visit(RepetitionAlternative alternative);
}

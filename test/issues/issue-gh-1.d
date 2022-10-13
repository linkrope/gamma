module test.issues.issue_gh_1;

import test.helper;

@("test GH issue #1 for unproductive start symbol")
unittest
{
    with (sandbox)
    {
        run!"cat test/issues/issue-gh-1.eag | ./gamma --output-directory %s"(directory)
            .shouldFailNotMatching("Error: undefined identifier P0")
            .shouldFail("error: start symbol Expr is unproductive");
    }
}

@("test GH issue #1 for unproductive non-start symbol")
unittest
{
    with (sandbox)
    {
        run!"cat test/issues/issue-gh-1-warn-only.eag | ./gamma --output-directory %s"(directory)
            .shouldMatch("warn: ExprTail unproductive");
    }
}

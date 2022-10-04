module test.issues.issue_gh_1;

import test.helper;

@("test for GH issue #1")
unittest
{
    with (sandbox)
    {
        run!"cat test/issues/issue-gh-1.eag | ./gamma --output-directory %s"(directory)
            .shouldFailNotMatching("Error: undefined identifier P0");
    }
}

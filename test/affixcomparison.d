module test.affixcomparison;

import std.path;
import test.helper;

// These tests run the compiler generator so that its built-in comparison of
// Gamma affix data against the legacy epsilon EAG data is exercised. Remove
// this module when that legacy comparison and the epsilon code are removed.

@("compare ordinary and composite affix forms")
unittest
{
    with (sandbox)
    {
        run!"%s --space %s --output-directory %s"(gamma, buildPath("example", "decl-appl.eag"), directory)
            .shouldPassWith("DeclAppl grammar is SLAG");
    }
}

@("compare numbered and negated affix variables")
unittest
{
    with (sandbox)
    {
        run!"%s --space %s --output-directory %s"(gamma, buildPath("example", "unequal.eag"), directory)
            .shouldPassWith("OberonO grammar is SLAG");
    }
}

@("compare affixes on direct EBNF wrappers")
unittest
{
    with (sandbox)
    {
        run!"%s --space %s --output-directory %s"(gamma, buildPath("example", "ebnf.eag"), directory)
            .shouldPassWith("S grammar is SLAG");
    }
}

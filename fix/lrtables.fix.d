module $;

import gamma.runtime.lr.LR1ParserTables;
import std.typecons : Nullable, nullable;

public immutable LR1ParserTables tables = LR1ParserTables(
    $,
    $,
    $,
    $,
    $,
    $,
    $,
    $,
);

public immutable Nullable!LexerCandidate[] lexerCandidates = $;

public immutable LexerRule[] lexerRules = $;

public immutable string[] terminalNames = $;

public immutable string[] nonterminalNames = $;
$

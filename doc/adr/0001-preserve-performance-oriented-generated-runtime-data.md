# Preserve performance-oriented data structures in generated compilers

Gamma may modernize its generator, but generated compilers shall retain
the compact, performance-oriented data structures established by Epsilon
across lexing, parsing, syntax-tree representation, and evaluation.
This applies equally to LL and LR parsing: lexical nonterminals and syntax rules
must build their evaluator-compatible tree fragments directly,
never an intermediate heap-object tree followed by a bridge transformation.

Future evaluator work must preserve these data-oriented runtime contracts,
or demonstrate a measured end-to-end improvement before replacing them.
This decision constrains generated compilers, not Gamma's generator domain model.

Compatibility is evaluator-observable rather than byte-identical: direct construction may
choose a different arena-address order when rule alternatives, child order, positions, and
evaluation are equal. A diagnostic-only renderer may combine compact-tree records with
generated source-rule traversal to reconstruct terminals for graphical parse-tree output;
that traversal is not part of evaluator traversal.

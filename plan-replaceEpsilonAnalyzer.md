# Plan: Replace epsilon.analyzer with gamma pipeline + EAG transformer

## TL;DR
Four phases. Integrate gamma's dormant Earley parser into gamma's analyzer (phase 1). Audit gamma parser parity against epsilon (phase 2). Build a new transformer module `src/gamma/input/EAGBuilder.d` that converts gamma's validated Grammar model into epsilon's global EAG buffers (phase 3). Finally swap out `epsilon.analyzer.Analyse()` in `main.d` (phase 4).

## Decisions
- Affix approach: Option B — integrate gamma's Earley parser first, skip epsilon's CheckSemantics; transform gamma's Term trees to epsilon's NodeBuf format
- Scope: replace ALL three phases of epsilon.analyzer (Specification + CheckSemantics + ComputeEAGSets)
- Transformer location: `src/gamma/input/EAGBuilder.d` (gamma already imports epsilon; dependency goes gamma→epsilon; independent of concrete syntax so NOT in epsilang/)
- EAGBuilder strategy: dual-mode compare→store; builder carries its own internal EAG representation; each sub-phase has a `compareX()` (diffs vs live EAG globals) that later becomes `storeX()`, enabling automatic regression diffing on every `dub test --build=unittest --config=example`
- EAGBuilder granularity: iterative sub-phases (meta first, then hyper, then affixes, then sets); single file with distinct methods rather than separate files

---

## Phase 1: Integrate gamma's Earley parser into gamma's analyzer
**Goal**: gamma's Grammar model comes out "fully validated" (affix forms semantically checked against meta grammar, Term trees stored)

Steps:
- [x] `src/gamma/input/earley/Parser.d` — implement the error reporting TODO at line 72; surface parse failures with position info
- [x] Ensure gamma's grammar model structs (Signature, HyperSymbolNode, Operator params in `src/gamma/grammar/affixes/`) can carry the validated `Term` trees — `Params` refactored to `size_t key + Position`; `HyperGrammar` created bundling `Grammar + Term[][]`; `PrintingHyperVisitor` updated; `epsilang/parser.d` collects `AffixForm[][] affixFormsByKey_`
- [x] `src/gamma/input/epsilang/analyzer.d` — after `parseSpecification()`, iterate over all nonterminal occurrences that carry Signatures; for each affix form call `earleyParser.parse(domain, affixForm)`; attach returned `Term` tree back to the model; report error on `null` return

Checkpoint: `dub test --build=unittest --config=example` — all tests pass (epsilon.analyzer still active, this only changes gamma's side validation)

---

## Phase 1½: Wire actual/end params through the parser and fix the hyper printer
**Goal**: EBNF expressions with params (`{ <…> … <…> }`, `[ <…> … <…> ]`) round-trip correctly through the model and are pretty-printed faithfully

Background: The parser currently passes `null` for `Operator.params` (actual params before `{`/`[`) and `Operator.endParams` (actual params after `}`/`]`), and `RepetitionAlternative` is also constructed with `null` for the closing params. Consequently `PrintingHyperVisitor` cannot print them. The `EBNFConverter` does push `repetition.rule.lhs` (which has the formal params key) into the outer RHS, so converted output is partially correct, but the actual params wrapping the EBNF expression are lost.

Steps:
- [x] **Parser TODO — `Operator.params`**: in `parseHyperTerm`, when an EBNF open bracket is preceded by actual params (`spareActualParams`), pass them to the `Group`/`Option`/`Repetition` constructor (first argument, currently `null`)
- [x] **Parser TODO — `Operator.endParams`**: in `parseHyperTerm`, after parsing the closing `]`/`}`, parse the following formal params (if present) and pass them as `endParams` to `Option`/`Repetition` (third argument, currently `null`)
- [x] **Parser TODO — `RepetitionAlternative.params`**: in `parseHyperExpr`, pass the trailing actual params (`undecidedActualParams` / `spareActualParams`) to `RepetitionAlternative` (third argument, currently `null`)
- [x] **Parser TODO — `HyperSymbolNode` lhs**: resolve all remaining `// TODO: which params?` comments in `parseHyperRule` and `parseHyperTerm` — for named symbols the trailing `undecidedActualParams` belongs to that node
- [x] **Printer fix — EBNF operator params**: in `PrintingHyperVisitor.visit(Repetition)` / `visit(Option)` / `visit(Group)`, print `operator.params` (actual params before `{`) and `operator.endParams` (actual params after `}`) using the same `<…>` format as `visit(SymbolNode)`, looking up terms via `termsByKey`; signature info (`+`/`-`) interleaved for formal params; `HyperGrammar` extended with `signaturesByKey` array; `RepetitionAlternative` lhs and trailing params printed

Checkpoint: `dub run -- example/abc.eag` pretty-prints the hyper grammar with all params visible; `dub test --build=unittest --config=example` still passes

---

## Phase 1¾: Per-nonterminal signatures — model, conflict checking, actual-vs-formal validation
**Goal**: the signature belongs to the nonterminal, not to an individual params occurrence; conflicts and arity errors are reported by gamma's analyzer; printing uses the signature directly

### Background — what epsilon does
- `EAG.HNont[Sym].Sig` — one signature (pointer into `DomBuf`) stored per hyper nonterminal; initially `-1`
- `SigOK(Sym)` — on every formal-params occurrence for `Sym`, compare the new signature against the stored one; if first occurrence, store it; if mismatch, return `false` → caller reports "formal params differ"
- `CheckParamList(HNont[x].Sig, actual, …)` — on every actual-params occurrence, verify arity matches the stored signature and direction is compatible

### What currently exists in gamma
- `Signature` is stored per params-key inside the parser's private `ParamsInfo`; exposed via `HyperGrammar.signaturesByKey` (flat array indexed by key, one entry per occurrence — wrong granularity)
- `Params` carries only `key + position`; no reference to the nonterminal's canonical signature
- No per-nonterminal signature map, no conflict check, no actual-vs-formal arity check

### Steps

- [x] **`HyperLhsNode` and `LhsNode`** (approach taken instead of `FormalParams extends Params`): `LhsNode : Node` stores `Nonterminal` directly; `HyperLhsNode : LhsNode` adds `Signature signature()` and `Params params()`; `Alternative.lhs` changed from `SymbolNode` to `LhsNode`; all `.lhs.symbol` casts replaced by `.lhs.nonterminal`; `HyperGrammar.signaturesByKey` removed
- [x] **Parser `FormalParams` struct** (parser-private, not a grammar model class): `parseHyperRule` / `parseHyperExpr` thread a `Nullable!FormalParams lhsFormal` pair instead of two separate `Signature` + `Params` variables; the struct exists only inside `parser.d`; formal params continue to produce a plain `Params` in the model, with the signature attached via `HyperLhsNode`
- [x] **Printer update**: `PrintingHyperVisitor` reads `HyperLhsNode.signature()` directly; two methods `printParams(Params)` / `printFormalParams(Signature, Params)` replace the old single method with a null-signature branch; `signaturesByKey` field and constructor parameter removed
- [ ] **`Analyzer` — per-nonterminal signature map**: after `parseSpecification`, walk all hyper rules; for each alternative whose `lhs` is a `HyperLhsNode` with a non-null signature, look up the nonterminal in a `Signature[Nonterminal]` map; if absent, store; if present and not structurally equal, report error "formal params differ"
- [x] **`parseAffixForms` — parse actual params**: after the per-nonterminal signature map is built, iterate over `paramsByKey` entries where `signature is null` (actual params); look up the nonterminal's signature from the map; if found, parse each affix form against the corresponding domain and fill `termsByKey[key]`; report error on `null` term — this is what makes the printer emit actual params correctly
- [x] **`Analyzer` — actual-vs-formal arity check**: for actual params entries, verify `affixForms.length == signature.length`; report error "number of affixforms differs from signature" on mismatch

Checkpoint: `dub test --build=unittest --config=example` — all tests pass; `dub run -- example/count1.eag` (or any grammar with formal params) reports no spurious errors; actual params are printed with their affix forms

---

## Phase 2: Parity audit — gamma parser vs epsilon analyzer
**Goal**: confirm gamma's parser handles every syntactic/semantic case epsilon does, and fix any gaps

Items to verify systematically:
- [x] Lexical rules (`*` marker): gamma stores in `lexicalHyperNonterminals` — verify round-trip matches epsilon's treatment; `getLexicalMetaNonterminals()` getter added (parallel to hyper); transitive closure in `GrammarProperties` intentionally not applied to meta side (epsilon has none)
- [x] WhiteSpace rules: both warn "not yet supported" — behaviour must be identical (no silent divergence); gamma was silently discarding; `warn!"skipping not yet supported whitespace rule\n%s"` added to `parseWhiteSpaceRule` to match epsilon exactly
- [x] Negation (`!` on variables): gamma stores `unequal_` flag on Variable — correctly parsed and carried through the Term tree; Earley parser need not enforce it (epsilon doesn't either — enforcement is a code-generator concern via `VarRecord.Neg`); flag must be consumed in `EAGBuilder.buildAffixes()` (Phase 3c)
- [x] Nested block comments: nesting logic equivalent — both track depth, handle `/* /* */ */`, error at EOF; gamma additionally tracks line numbers inside comments (advantage); epsilon uses `dchar` vs gamma's `char` but irrelevant for ASCII EAG files; no action needed
- [x] Error messages: gamma should produce equivalent or better diagnostics for every error path in epsilon's Specification(); wording audit done — most differences are trivial quote-style variations; fixed: `"meta-variable expected"` → `"meta-nonterminal expected"` (after `!` with no name); `"! operator not allowed"` and `"variable never on defining position"` deferred to Phase 3c (require full affix flow analysis); start symbol signature check deferred to step 6
- [x] Start symbol validation: `error!"start symbol %s must have exactly one synthesized attribute"` added to `src/gamma/input/epsilang/analyzer.d` after the productivity guard; checks `HyperLhsNode` cast (null → zero params), `sig.length != 1`, and `sig.direction[0] != Direction.output`

File to patch if gaps found: `src/gamma/input/epsilang/parser.d`, `src/gamma/input/epsilang/analyzer.d`

Checkpoint: manual review + `dub test --build=unittest --config=example`

---

## Phase 2½: Shrink — merge named nonterminal with its sole EBNF operator in the parser

**Goal**: when a named rule's entire RHS is a single EBNF operator (`()`, `[]`, `{}`) with formal params and nothing else, the parser must NOT create a separate anonymous nonterminal. The named nonterminal *is* the operator. Fixing this at the grammar-model level eliminates all downstream workarounds.

### Background — what epsilon does

Epsilon's `Shrink` pass (called from `Specification()`) walks every hyper alternative. If it finds an `EAG.Grp` factor that is the sole factor in the alternative, carries no actual params, and whose body alternatives have formal params (i.e. an anonymous nonterminal whose rule has the shape `<formals>: body <formals>.`), it merges: `HNont[namedSym]` takes the signature and the body alternatives of the anonymous nonterminal directly. The anonymous nonterminal entry is then unused.

### What gamma currently does instead

The parser creates an anonymous nonterminal via `hyperGrammarBuilder.buildAnonymousNonterminal`, uses it as the lhs of the EBNF body, and patches around the two-nonterminal discrepancy:
- `parser.d` registers the anonymous nonterminal's signature under the named nonterminal via `signatureByNonterminal[enclosingNonterminal]` (signature trick, lines ~574–587)
- `EAGBuilder.buildAffixes()` contains a `CheckRep` imitation to detect and move `undecided` params that epsilon would never have created

### Plan

- [ ] **Parser — detect the Shrinkable pattern at the point of EBNF operator creation**: after `parseHyperExpr` returns and `rule` is built, check:
  1. `hasFormalParams` — the anonymous nonterminal's lhs has a signature
  2. `nodes.empty` — nothing preceded the operator in this alternative (checked *before* `nodes ~= operator`)
  3. `enclosingNonterminal` is not an `AnonymousNonterminal` — we are inside a named rule
  4. Nothing follows: current `lexer.front` is a terminator (`|`, `.`, `)`, `]`, `}`, or empty)

  When all four hold: instead of using `identifier` (freshly created anonymous nonterminal), patch the alternatives so their `lhs.nonterminal` is `enclosingNonterminal` (or build them that way from the start by passing `enclosingNonterminal` to `parseHyperExpr`). The `Operator` node inserted into the outer `nodes` then references `enclosingNonterminal` as the operator's rule's lhs — no anonymous nonterminal is created.

- [ ] **Remove signature trick from `parser.d`**: delete the `signatureByNonterminal[enclosingNonterminal]` block (currently lines ~574–587); it is no longer needed because the body alternatives already have the correct lhs nonterminal.

- [ ] **Remove `CheckRep` imitation from `EAGBuilder.buildAffixes()`**: delete the `repActualIsUndecided` block and the `affix_wellMatchedEmpty` helper; with the grammar model correct, the `repAlt.params` situation that triggered the imitation no longer arises.

- [ ] **Remove the `open != '('` guard removal** (the last parser.d fix): the Shrinkable-pattern detection now handles all three bracket types uniformly; the explicit guard is moot.

- [ ] **Simplify `buildHyper` and `compareHyper`** in `EAGBuilder.d`: remove any code paths that special-case named-vs-anonymous nonterminal merging; the grammar model now tells the truth.

Checkpoint: `dub test --build=unittest --config=example` — all tests pass with the Shrink fix in place and workarounds removed

---

## Phase 3: Build EAGBuilder iteratively — dual-mode compare→store

**New file**: `src/gamma/input/EAGBuilder.d`

**Core architecture**: EAGBuilder carries its **own internal representation** (fields mirroring the EAG global arrays). Sub-phases are added one by one. Each sub-phase has two methods:
- `buildX(...)` — fills the builder's own fields from gamma's Grammar model
- `compareX()` — diffs the builder's fields against the live EAG globals (already populated by epsilon.analyzer) and reports mismatches

Because epsilon.analyzer still runs first in `main.d`, the comparison runs automatically on every `dub test --build=unittest --config=example` invocation with zero extra tooling.

**Integration wiring in `main.d` during Phase 3:**
```
analyzer.Analyse(input);      // epsilon fills EAG globals as before
builder.buildMeta(metaGrammar);
builder.compareMeta();         // logs/asserts diffs — free regression check
// add buildHyper/compareHyper ... incrementally
```

**Transition trigger**: when ALL `compareX()` sub-phases report zero diffs consistently → implement `storeAll()` (see 3e) that writes all EAG globals in one coordinated pass and replaces all `compareX()` calls. The store sub-phases cannot be activated individually because gamma's index ordering differs from epsilon's: partial stores leave the EAG globals in an inconsistent state.

### 3a — Meta rules
- [x] `buildMeta(Grammar metaGrammar)`: walk meta grammar; intern names; fill builder's `MNontRecord[]`, `MAlt[]`, `MembBuf[]` mirrors
- [x] `compareMeta()`: diff builder arrays vs `EAG.MNont[]`, `EAG.MAlt[]`, `EAG.MembBuf[]`; report field + index of each mismatch; uses Id-bijection maps (symbolTable Id → array index) so ordering differences between gamma and epsilon are tolerated

### 3b — Hyper grammar structure
- [x] `buildHyper(Grammar hyperGrammar)`: fill builder's `HNontRecord[]`, linked `Alt`/`Factor` lists; replicate exact `Prev`/`Next`/`Sub`/`Last` pointer layout
- [x] `compareHyper()`: diff against `EAG.HNont[]`, walking the Alt/Factor chains structurally; translate embedded MNont/MTerm references through the same Id-bijection maps used in `compareMeta()`
- Reference: epsilon/analyzer.d Specification() for exact buffer/pointer layout

- [ ] **Pending simplification**: once the parser performs Shrink (merging the named nonterminal with its sole-EBNF-operator anonymous nonterminal in the grammar model), the workarounds in `buildHyper` and `buildAffixes` that compensate for the grammar model having two distinct nonterminals where epsilon sees one will need to be removed.

### 3c — Affix forms / parameter model
- [ ] `buildAffixes()`: walk `Term` trees from Phase 1 (Variable/Composite hierarchy); emit builder's `VarRecord[]` (Def, Neg, Num, Sign), `NodeBuf[]`, `MSymBuf[]`, `ParamRecord[]`, `ScopeDesc[]`; pure format conversion — no re-parsing
- [ ] `compareAffixes()`: diff against EAG globals; translate symbol references through bijection maps
- Reference: epsilon/analyzer.d CheckSemantics(), epsilon/earley.d, epsilon/eag.d

### 3d — EAG sets
- [ ] `buildSets()`: convert gamma's `GrammarProperties` nullable/productive/reachable to builder's BitArray mirrors
- [ ] `compareSets()`: diff against `EAG.Reach[]`, `EAG.Prod[]`, `EAG.Null[]`; translate symbol references through bijection maps
- Reference: epsilon/analyzer.d ComputeEAGSets()

Checkpoint per sub-phase: `dub test --build=unittest --config=example` — compare functions run automatically; mismatch output drives the next fix iteration

### 3e — Store all (after all compare steps confirm zero diffs)
Store all sub-phases must happen together in one pass. Storing partial results while epsilon's EAG globals are still intact would leave the arrays in an inconsistent state: epsilon's HNont/Alt/Factor entries embed MNont indices using epsilon's ordering; gamma's storeMeta() would overwrite MNont with gamma's ordering; the cross-references would no longer match.

Therefore, once all `compareX()` report zero diffs on every example grammar:
- [ ] Implement `storeAll()` that writes ALL EAG globals in a single coordinated pass using a single consistent indexing scheme (gamma's or a newly agreed canonical order); all cross-references (MNont refs inside HNont entries, etc.) are emitted using the same scheme
- [ ] Remove all `compareX()` calls from `main.d`; replace with single `storeAll()` call
- [ ] Delete `epsilon.analyzer.Analyse()` call from `main.d`

---

## Phase 4: Replace epsilon.analyzer in main.d
- [ ] `src/gamma/main.d`: `check()` already calls gamma's analyzer; refactor so the analyzed Grammar models are accessible to `compile()`
- [ ] In `compile()`: replace `analyzer.Analyse(input)` (line ~96) with call to `EAGBuilder.storeAll(metaGrammar, hyperGrammar)`
- [ ] Move the dual-use lexer (`src/epsilon/lexer.d`) into `src/gamma/`; update all imports
- [ ] Remove `src/gamma/input/epsilang/Scanner.d` (marked unused) now that the epsilon lexer is superseded
- [ ] Remove `epsilon.analyzer` import once confirmed
- [ ] Verify `Predicates.Check()` and all downstream generators still work unchanged (they read EAG globals, which are now populated by the transformer)

Checkpoint: `dub test --build=unittest --config=example` with epsilon.analyzer removed — all tests pass

---

## Relevant files
- `src/gamma/input/epsilang/analyzer.d` — Phase 1: wire in Earley validation
- `src/gamma/input/earley/Parser.d` — Phase 1: add error reporting
- `src/gamma/input/earley/AffixForm.d`, `Item.d`, `ItemSet.d` — may need minor tweaks in Phase 1
- `src/gamma/grammar/affixes/` — Phase 1: ensure Term trees are stored in model
- `src/gamma/input/epsilang/parser.d` — Phase 2: patch any parity gaps
- `src/gamma/input/EAGBuilder.d` (NEW) — Phase 3: core transformer
- `src/gamma/main.d` — Phase 4: swap epsilon.analyzer call
- `src/epsilon/analyzer.d` — reference impl for exact buffer layout (read-only during this work)
- `src/epsilon/eag.d` — target data model (read-only)
- `src/epsilon/earley.d` — reference for NodeBuf format (read-only)

## Verification

> **Note**: `dub test --build=unittest --config=example` must be run from a **WSL terminal**. The `preBuildCommands` in `dub.json` use `$DUB` (a Unix environment variable) and the generated binaries are Linux ELF executables.

1. `dub test --build=unittest --config=example` after each phase and each 3x sub-phase
2. `compareX()` methods in Phase 3 make diffs automatic on every test run — no separate tooling needed
3. After Phase 4: full `dub test --build=unittest --config=example` with epsilon.analyzer removed

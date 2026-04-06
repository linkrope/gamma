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

- [ ] **`FormalParams` class**: add `src/gamma/grammar/hyper/FormalParams.d` — extends `Params`, adds `Signature signature()` property; actual params remain plain `Params`; the two types are distinguishable by `cast`
- [ ] **Parser uses `FormalParams`**: in `parseParams(Yes.formalParams)`, construct `new FormalParams(key, signature, position)` instead of bare `Params`; keep `Params` for actual params; update `ParamsInfo.params` accordingly
- [ ] **`HyperGrammar.signaturesByKey` removal**: drop the `signaturesByKey_` field and its constructor parameter added in Phase 1½; the printer will look up the signature from the `FormalParams` node itself (see printer step below)
- [ ] **`Analyzer` — per-nonterminal signature map**: after `parseSpecification`, walk all hyper rules; for each `HyperSymbolNode` whose `params` is a `FormalParams`, look up the nonterminal by index in a `Signature[size_t]` map; if absent, store; if present and not structurally equal, report error "formal params differ" (use `addError` at `params.position`)
- [ ] **`Analyzer` — actual-vs-formal arity check**: for each `HyperSymbolNode` whose `params` is a plain `Params` (actual params), look up the nonterminal's signature; if found, verify `terms[key].length == signature.length`; report error "number of affixforms differs from signature" on mismatch
- [ ] **Printer update**: in `PrintingHyperVisitor.printParams`, check `if (auto fp = cast(FormalParams) params)` and use `fp.signature.direction` for `+`/`-` prefixes; remove the `signaturesByKey` field and constructor parameter

Checkpoint: `dub test --build=unittest --config=example` — all tests pass; `dub run -- example/count1.eag` (or any grammar with formal params) reports no spurious errors

---

## Phase 2: Parity audit — gamma parser vs epsilon analyzer
**Goal**: confirm gamma's parser handles every syntactic/semantic case epsilon does, and fix any gaps

Items to verify systematically:
- [ ] Lexical rules (`*` marker): gamma stores in `lexicalHyperNonterminals` — verify round-trip matches epsilon's treatment
- [ ] WhiteSpace rules: both warn "not yet supported" — behaviour must be identical (no silent divergence)
- [ ] Negation (`!` on variables): gamma stores `unequal_` flag on Variable — confirm it is honoured in Earley integration
- [ ] Nested block comments: verify gamma scanner handles `/* /* */ */` like epsilon lexer does
- [ ] Error messages: gamma should produce equivalent or better diagnostics for every error path in epsilon's Specification()
- [ ] Start symbol validation (epsilon checks "exactly one synthesized attribute") — add to gamma if missing

File to patch if gaps found: `src/gamma/input/epsilang/parser.d`, `src/gamma/input/epsilang/analyzer.d`

Checkpoint: manual review + `dub test --build=unittest --config=example`

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

**Transition trigger**: when `compareX()` reports zero diffs consistently → rename to `storeX()` and have it write to EAG globals instead of comparing. When all sub-phases use `storeX`, proceed to Phase 4.

### 3a — Meta rules
- [ ] `buildMeta(Grammar metaGrammar)`: walk meta grammar; intern names; fill builder's `MNontRecord[]`, `MAlt[]`, `MembBuf[]` mirrors
- [ ] `compareMeta()`: diff builder arrays vs `EAG.MNont[]`, `EAG.MAlt[]`, `EAG.MembBuf[]`; report field + index of each mismatch
- [ ] `storeMeta()`: replace `compareMeta()` once zero diffs confirmed

### 3b — Hyper grammar structure
- [ ] `buildHyper(Grammar hyperGrammar)`: fill builder's `HNontRecord[]`, linked `Alt`/`Factor` lists; replicate exact `Prev`/`Next`/`Sub`/`Last` pointer layout
- [ ] `compareHyper()`: diff against `EAG.HNont[]`, walking the Alt/Factor chains structurally
- [ ] `storeHyper()`: replace `compareHyper()` once zero diffs confirmed
- Reference: epsilon/analyzer.d Specification() for exact buffer/pointer layout

### 3c — Affix forms / parameter model
- [ ] `buildAffixes()`: walk `Term` trees from Phase 1 (Variable/Composite hierarchy); emit builder's `VarRecord[]` (Def, Neg, Num, Sign), `NodeBuf[]`, `MSymBuf[]`, `ParamRecord[]`, `ScopeDesc[]`; pure format conversion — no re-parsing
- [ ] `compareAffixes()`: diff against EAG globals
- [ ] `storeAffixes()`: replace `compareAffixes()` once zero diffs confirmed
- Reference: epsilon/analyzer.d CheckSemantics(), epsilon/earley.d, epsilon/eag.d

### 3d — EAG sets
- [ ] `buildSets()`: convert gamma's `GrammarProperties` nullable/productive/reachable to builder's BitArray mirrors
- [ ] `compareSets()`: diff against `EAG.Reach[]`, `EAG.Prod[]`, `EAG.Null[]`
- [ ] `storeSets()`: replace `compareSets()` once zero diffs confirmed
- Reference: epsilon/analyzer.d ComputeEAGSets()

Checkpoint per sub-phase: `dub test --build=unittest --config=example` — compare functions run automatically; mismatch output drives the next fix iteration

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

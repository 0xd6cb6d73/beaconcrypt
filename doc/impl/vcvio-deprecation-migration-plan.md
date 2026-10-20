# Migrating the deprecated VCVio probability API on the current pin: staged plan

Status: binding plan of the VCVio deprecation migration. Copied verbatim below this paragraph from the survey output `/tmp/bc-arc-scratch/vcvio-survey/plan.md` (sha256 bd20443e3fc9f9a4a2810eca5f12d9b671417beacea398ac9663a4ea129b09a0). The owner accepted it on 2026-10-19 with the recommended answers D1 to D5 and D8 to D11 of section 11, phase B of D6 included (proofs of each stage's files are rewritten off the deprecated layer while the files are open, plus a final sweep), and D7 as Lean-level checks for every stage (accepted with a full `verify-in-shell` after S3, S6 and S9, which the owner's revision of D7 in the [Amendments](#amendments) removed: no stage runs `verify-in-shell`). The counts are those of central `8f81b003`; each stage re-measures them on its own base, and the stage records in [`staged-verification-record.md`](staged-verification-record.md) give the measured values. Two later changes bind the plan and are recorded in the section [Amendments](#amendments) at the end: amendment A1 (2026-10-19) keeps every notation, tactic, command and other metaprogram out of the build, and the owner's revision of D7 (2026-10-19, `decision-2026-10-19.txt` item 5) drops the full `verify-in-shell` from the whole migration.

Survey lane 2, task "survey plan", 2026-10-19. Owner direction of 2026-10-19: do not bump VCVio, Lean or Mathlib; follow the VCVio deprecation warnings on the current pin `98dc1089` so that the later move to the newest VCVio is easy. This plan is read-only work: nothing was written to any repository. Inputs are `pin-replacements.md/.json`, `usage.md/.json`, `api-map.md/.json` and `stack.md` in `/tmp/bc-arc-scratch/vcvio-survey/`, plus one new Lean probe and a few scripts in `/tmp/bc-arc-scratch/vcvio-survey/plan/` (section 15). All numbers are for central `origin/codex/full-proof-composition` at `8f81b003` and must be re-measured on the base the work starts from (section 8, step 1).

## 1. Summary

- **Scope.** The project uses five deprecated VCVio declarations in 1753 source sites in 246 files. 1359 sites warn and 394 are hidden by 183 `set_option linter.deprecated false` lines. The sites put the deprecated API in 720 theorem statements (`Pr[= x | mx]`, `Pr[p | mx]`, `𝒮[mx]`), in the bodies of 36 project wrapper definitions (advantages, losses and event probabilities, which 615 further theorem statements use), and in 545 proof sites. Following the warnings therefore mostly means restating theorems, not renaming lemmas.
- **Approach.** The work runs in ten stages, S0 to S9, each landable on its own with a full build and checks. S0 adds a project probability shim layer for the four VCVio families (EvalDist, OracleComp, ProbabilityTheory, ProgramLogic) and a single transitional bridge module. S1 to S9 then migrate the `Computational` families bottom-up along the project's reference graph, which has eleven levels and only two small cycles, each merged into one stage.
- **Replacement vocabulary.** It is upstream's final vocabulary, all of which exists at the pin or is backported by the shim. Events and outputs use `Pr{let x ← mx}[p x]`, which needs no measurable space. Equality of distributions uses `A =ᵈ B`. `𝒟[…]` measures are kept as they are. The upstream codemod produces exactly these forms, so it can do the mechanical part once its pin-incompatible rewrites are filtered out.
- **Statements are not weakened.** Every theorem and definition outside a stage's restatement allowlist keeps its elaborated type, checked by type hash. This covers all 615 theorems stated through wrappers, including the 352 `PqxdhDeployment*` headline statements, so they keep their exact statements. Each restated declaration keeps its name and `#print axioms` guard and gets an iff certificate against its exact old elaborated statement, checked by hash. No hypotheses are added, no instance binders are added and no global instances are introduced.
- **Effort.** About 23 to 51 agent-days in total, with a central estimate near 30: S0 3 to 5 days, S1 to S9 between 1 and 8 days each. Machine time comes on top: four or five full Lean builds of about 25 minutes each per stage, plus one `verify-in-shell` of about 5.5 hours per landing, if the owner keeps that cadence (D7).
- **First increment.** S0 plus the S1 pilot: the shim and bridge, the 29 proof-only sites (21 warnings) that need no statement change, and the CTX-reduction and VCVio-feasibility modules (22 sites, 4 theorems, 18 wrappers, no cross-stage consumers). It is followed by a go/no-go review that recalibrates the estimates (section 13).
- **Owner decisions and prerequisite.** Eleven decisions are needed (section 11). The most important are permission to edit published (frozen) modules and the pinned `PqxdhJointIdentity.lean`, and the certificate and bridge policy. Lane 1 (`codex/lean-warning-cleanup` at `c1b6e475`, not yet on central) must land first.

## 2. Baseline

| Measure | Value | Source |
| --- | --- | --- |
| Deprecated VCVio declarations used | `probEvent` 871 sites, `evalSPMF` 532, `probOutput` 323, `ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage` 15, `SPMF` 12; `probFailure` only inside VCVio-produced proof terms (62 declarations) | usage §3 |
| Sites: warned / suppressed | 1359 / 394; suppression: 183 lines in 62 files, 5 of them file-wide | usage §9 |
| Sites by use | statement 1171, proof 545, definition body 37 | usage §4 |
| Theorems with the API in the statement | 720 (541 with a `#print axioms` guard) | usage §5 |
| Direct wrappers / indirect wrappers / theorems stated only through wrappers | 36 / 65 / 615 | usage §6 |
| Proof-term-only theorems (facade lemmas, no source site) | 271 | usage §4 |
| Output types at deprecated applications in statements | 127 ready for a measure form, 474 generic, 110 concrete without `MeasurableSpace`, 9 both | usage §5 |
| Monads at deprecated applications in statements and wrapper bodies | 776 application kinds: 766 `ProbComp`, 10 `OracleComp` with concrete specs. Every one synthesizes `EvalDistSemantics`, `LawfulEvalDistSemantics` and `LawfulMonad` and has its output in `Type`, so `Pr{…}` and `𝒟[…]` elaborate everywhere | new probe, `plan/probe-out/monads.tsv` |
| Project-internal references into the restated declarations | 3908 edges; 760 cross-module edges into the 756 restated declarations (720 theorems + 36 wrappers) | new probe, `plan/probe-out/edges.tsv` |
| Project shim layer for probability | none today; every wrapper lives in a `Computational` module | usage §8 |

The family-level reference graph (`plan/data/levels.json`) is a DAG once two small cycles are merged: {PqxdhJoint*, PqxdhDynamic*, PqxdhPhase1*} and {PqxdhInitial*, PqxdhAuthenticated*}. Its longest chain has eleven levels, from leaves such as `CtxRom*`, `PqxdhSecret*` and `PqxdhProjection*` (level 0) to `PqxdhDeployment*` (level 10). With the stage assignment of section 7, no module of an earlier stage references a declaration restated in a later stage (0 violations).

## 3. Target vocabulary at the pin

Following the warnings means removing every use of the deprecated constants. Where the attribute's literal suggestion and upstream's final idiom differ, the plan uses the upstream idiom. Both are non-deprecated at the pin, and the upstream idiom is the form the newest VCVio uses (decision D2).

| Deprecated form | Replacement used | Needs at the pin | Upstream afa6593f |
| --- | --- | --- | --- |
| `Pr[= x \| mx]` (`probOutput`) | `Pr{let y ← mx}[y = x]`; `𝒟[mx] {x}` only where a measure lemma consumes it and `α` has measurable singletons (Bool, Fin) | nothing on `α` (the pin macro gives `𝒟[do …] {True}` on `Prop`) | same source text; `Pr{…}` now elaborates to `prEvent (p <$> mx)` |
| `Pr[p \| mx]` (`probEvent`) | `Pr{let x ← mx}[p x]` | nothing on `α` | same source text |
| `𝒮[A] = 𝒮[B]` (180 statements) | `A =ᵈ B` (`EvalDistEq`, backported by the shim) | nothing on `α` | `EvalDistEq` with identical definition text |
| `𝒮[mx]` in other positions (68 occurrences in 28 files after the codemod) | `Pr{…}`, `=ᵈ` or `𝒟[…]`, case by case | as for the chosen form | unchanged forms |
| `SPMF` in proofs (12) | measure forms; the four `SPMF` sites (with ten `𝒮` sites) in the `SPMF.Coupling` proofs of `product_coupling` and `relTriple_support` disappear by using VCVio's `relTriple_prod` (S0) | import `VCVio.ProgramLogic.Relational.FromUnary` (exists at the pin and upstream) | `relTriple_prod` same statement, now in `Relational.Basic` |
| `ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage` (15 proof sites) | the attribute's replacement `ProbComp.evalDist_apply_true_le_add_ofReal_boolDistAdvantage`, reached through one shim lemma | nothing | the replacement itself is removed upstream (e3d83efa). The shim lemma's ℝ≥0∞ form `𝒟[p] {true} ≤ 𝒟[q] {true} + ENNReal.absDiff …` is upstream's `Measure.apply_true_le_add_boolDist` by unfolding (check U3) |
| `probFailure` | not written by the project; if needed, `1 - 𝒟[mx] Set.univ` | — | `prFail` |

Rules that keep the replacements forward-compatible and faithful:

- **No instance binders, no global instances.** Never add `[MeasurableSpace α]`, `[DiscreteMeasurableSpace α]` or `[MeasurableSingletonClass α]` binders to a statement (it would weaken it), and never declare global `MeasurableSpace` instances on project types (they risk diamonds with product σ-algebras). `Pr{…}` and `=ᵈ` need neither. A `letI : MeasurableSpace α := ⊤` is allowed only inside proofs.
- **Forbidden in new code: names absent or changed upstream.** Do not use these:
  - `prEvent_eq_evalDist_decide_of_discrete` (use `prEvent_eq_evalDist_decide`);
  - `prEvent_bind_eq_lintegral` (use `prEvent_bind_eq_lintegral_of_discrete`);
  - `evalDist_bind_apply_univ` (its explicit argument changes);
  - `OracleComp.evalDist_query` and `OracleComp.evalDist_liftM_query` (their right-hand side becomes a `trim`);
  - `OracleComp.mem_support_iff_evalDist_singleton_pos_of_fullSupport` (its hypothesis is restated);
  - `OracleComp.ae_of_forall_mem_support` (backported as `evalDist.ae_of_forall_mem_support`);
  - `mem_support_iff_evalDist_singleton_ne_zero` (use `OracleComp.mem_support_iff_evalDist_singleton_pos`);
  - every `SPMF.toMeasure*` and `DiscreteEvalDistCompatible` bridge, which are allowed only inside the shim and the bridge module.

  Gate G5 enforces this (section 9).
- **No `rfl`, `change` or `show` through the `Pr{…}` expansion.** At the pin `Pr{…}` is a macro for a bind form, but upstream it is a head constant (check U6). Use the named laws (`prEvent_eq_evalDist*`, `prEvent_map`, `prEvent_bind_congr`, the backports).
- **No reliance on the pin's simp bridges in migrated proofs.** At the pin, `simp` turns `𝒟[mx] {x}` back into the façade through the `@[simp]` bridges `evalDist_apply_singleton`, `evalDist_apply_setOf` and `evalDist_apply_univ` (C6a), which upstream lacks (U7). Prefer `simp only` with measure, event or backport lemmas, or `simp [-evalDist_apply_singleton, -evalDist_apply_setOf, -evalDist_apply_univ]`. Remaining uses are counted by gate G5 as upgrade residual.

## 4. Shim layer (stage S0)

The project has no probability shim modules today. S0 creates four forward shims and one transitional bridge module, all flat in `Computational/` like every other project module. They import only VCVio, ToMathlib and Mathlib, plus each other in the order below, so every migrated module can import them without import cycles.

| Module (to be registered before creation) | Imports | Content |
| --- | --- | --- |
| `BeaconcryptCore.Computational.VCVioForwardEvalDist` | VCVio EvalDist, ProbabilityNotation | backport of `EvalDistEq` and `=ᵈ` (definition text identical to upstream: `∀ p, Pr{let x ← mx}[p x] = Pr{let y ← my}[p y]`), with `refl`/`symm`/`trans`/`Trans`, `map`, `bind_left`, `bind_right`, `prEvent_eq`, `of_forall_prEvent_eq`, `of_evalDist_eq`, `evalDist_eq` and `evalDistEq_iff_evalDist_eq`; monad-generic event laws absent at the pin (`prEvent_pure`, `prEvent_le_one`, `prEvent_ne_top`, `prEvent_false`, `prEvent_or_le`, `prEvent_exists_finset_le`, `prEvent_bind_const`, `prEvent_bind_le_of_forall_le`, `prEvent_bind_le_prEvent_of_support`, `prEvent_bind_le_prEvent_add`, `prEvent_bind_mono_of_forall_le_of_support`, `prEvent_eq_zero_of_not_mem_support`, `prEvent_eq_zero_of_forall_mem_support`, `prEvent_congr_of_support`, `prEvent_mono_of_support`, `prEvent_true_eq_evalDist_apply_univ`, `evalDist.ae_of_forall_mem_support`) |
| `BeaconcryptCore.Computational.VCVioForwardOracleComp` | the EvalDist shim; VCVio OracleComp EvalDist and SampleableType modules already in the closure | `OracleComp.prEvent_bind_eq_tsum`, `OracleComp.prEvent_eq_tsum_ite`, `OracleComp.lintegral_evalDist_eq_tsum`, `OracleComp.tsum_prEvent_le_one`, `OracleComp.prEvent_true_eq_one`, `OracleComp.prFail_eq_zero` (only if a stage needs `prFail`), `OracleComp.prEvent_bind_const`, `OracleComp.prEvent_bind_mono_of_support`, `OracleComp.EvalDistEq.bind_congr_of_support`, `OracleComp.EvalDistEq.bind_const`, `OracleComp.EvalDistEq.bind_bind_swap`, `OracleComp.evalDistEq_of_forall_prEvent_eq_output`, `SampleableType.prEvent_uniformSample_eq_singleton`, `SampleableType.prEvent_uniformSample`, `SampleableType.map_uniformSample_evalDistEq_of_bijective` |
| `BeaconcryptCore.Computational.VCVioForwardProbabilityTheory` | the OracleComp shim, `ToMathlib.MeasureTheory.Measure.Bool` | the Boolean bound in ℝ≥0∞ form, `𝒟[p] {true} ≤ 𝒟[q] {true} + ENNReal.absDiff (𝒟[p] {true}) (𝒟[q] {true})` (C7e), and the pin-only equation `ENNReal.ofReal (p.boolDistAdvantage q) = ENNReal.absDiff …` (C7d), both under project names because the upstream statement uses an ℝ≥0∞ `boolDist` that the pin does not have |
| `BeaconcryptCore.Computational.VCVioForwardProgramLogic` | the OracleComp shim, `VCVio.ProgramLogic.Relational.FromUnary` | re-export point for `relTriple_prod` and any relational helper the stages need |
| `BeaconcryptCore.Computational.VCVioLegacyBridge` (transitional, pin-only) | the EvalDist and OracleComp shims | about six old↔new bridge lemmas without instance hypotheses (`Pr[= x \| mx] = Pr{let y ← mx}[y = x]`, `Pr[p \| mx] = Pr{let x ← mx}[p x]`, `𝒮[A] = 𝒮[B] ↔ A =ᵈ B`, and the variants the 10 `OracleComp` applications need), each under an explicit `set_option linter.deprecated false in`. Also the `vcvio_legacy` simp set, the `vcvio_legacy_twin` command (section 5.2) and the certificate checker command. This is the only file allowed to contain deprecated syntax. |

The backport list (about 45 declarations) is the set of upstream replacements of the façade lemmas the project uses that are absent from the pin closure (`pin/facade-replacements.json`, 32 names, plus the `EvalDistEq` API and the forbidden-name substitutes). The ten most used are listed below; the counts are the project modules that use the façade lemmas they replace (summed over those lemmas, so a module can count twice):

- `EvalDistEq.bind_right` and `OracleComp.EvalDistEq.bind_congr_of_support`: 84 modules (`evalSPMF_bind_congr'`, `evalSPMF_bind_congr`, `evalSPMF_bind_congr_left`);
- `OracleComp.prEvent_bind_eq_tsum`: 79;
- `EvalDistEq.evalDist_eq`: 66;
- `prEvent_ne_top`: 62;
- `prEvent_pure`: 55;
- `prEvent_bind_le_of_forall_le`: 43;
- `prEvent_eq_zero_of_not_mem_support`: 37;
- `prEvent_congr_of_support`: 36;
- `prEvent_or_le`: 25.

Three rules govern the shim:

- **Upstream names, upstream statements (D3).** Backports carry upstream's name in upstream's namespace and upstream's statement text, with the pin's binder classes where upstream renamed them (`IsMeasureSpec` instead of `AnswerMeasure`). Each name must be absent from the whole pin package, not only from the closure. Two names occur in pin sources outside the closure (`SampleableType.prEvent_uniformSample` in `…SampleableType.NativeMeasure`, and the `OracleComp.EvalDistEq.bind_bind_swap` mention in `ToMathlib/…/IndependentDraws.lean`). For those, import the pin module if its statement matches upstream, otherwise backport and never import it.
- **Proofs may use anything at the pin.** The proofs of the shim and the bridge may use the façade, `DiscreteEvalDistCompatible` and the SPMF bridges. Statements outside `VCVioLegacyBridge` may not use deprecated syntax.
- **Forward replay check.** A scratch file states every backport's text and proves it with the upstream constant of the same name (`example : <statement> := @Name`). It runs through `coord.sh lean` against the existing afa6593f scratch build in `api/vcvio-upstream`, as the U-checks did. A failure means the backport is renamed into the project namespace (`BeaconcryptCore.VCVioForward`) and listed in the upgrade notes.

At the upgrade, the four forward shims lose their bodies and stay as thin modules that import the upstream modules, so no migrated file has to change its imports. `VCVioLegacyBridge` is deleted together with every `vcvio_legacy` use, which are greppable and counted.

S0 also makes the proof-only changes that need no statement change. These are the 15 Boolean-bound sites (through the ProbabilityTheory shim) and the two private copies of `relTriple_prod` (`PqxdhFirstRecordStopTagged.product_coupling` and `PqxdhServerAuthEntrySimulation.relTriple_support`, whose proofs become `relTriple_prod …`). Together they remove 29 sites and 21 warnings without touching any statement.

## 5. Statement policy

### 5.1 Rules

1. **No declaration is deleted or renamed.** Gate G4 compares full declaration dumps before and after each stage, using lane 1's `DeclsAll` tool: module, name, kind, universe parameters, type hash and definition value hash for all 95 092 constants.
2. **Every type outside the stage allowlist is unchanged.** The allowlist holds the stage's statement-direct theorems, its direct wrappers, and the auxiliary equation and congruence lemmas Lean derives from them. In particular, the 615 theorems stated through wrappers and the 65 indirect wrappers keep their elaborated statements exactly: their types name the wrapper constant, whose type does not change.
3. **Restated theorems keep their name, binders and guard.** Each restated theorem keeps its name, its binder list (no added hypotheses or instance binders), and its `#guard_msgs in #print axioms` guard, whose message must stay `[propext, Classical.choice, Quot.sound]`. Only the probability subterms change, through the vocabulary of section 3.
4. **Wrappers keep their name and type.** Only their body changes. Every theorem stated through a wrapper then keeps its text, and its meaning is tied to the old one by the wrapper's certificate (5.2).
5. **The deprecated form is not kept in the build.** Restated declarations do not keep the deprecated form as a second permanent statement in the build: that would keep deprecated syntax, and the old form ceases to exist upstream anyway. The old form survives only in the certificates of 5.2.

### 5.2 Certificates and transitional twins

The `vcvio_legacy_twin T` command (in `VCVioLegacyBridge`) computes T's old statement from its new elaborated type by inverting the vocabulary map:

- `Pr{let y ← mx}[y = x]` ↦ `probOutput mx x`;
- `Pr{let x ← mx}[p x]` ↦ `probEvent mx p`;
- `A =ᵈ B` ↦ `evalSPMF A = evalSPMF B`.

It proves `S_new ↔ S_old` with the bridge lemmas and adds `T_vcvioLegacy : S_old`. Because the old type is built programmatically, it contains no deprecated syntax and raises no warning, and it can be compared exactly with the base build. A certificate passes only if the generated old type has the same type hash, and the same `pp.all` text, as T in the pre-stage declaration dump. If the inverse map does not reproduce the old type exactly, the fallback is a textual twin copied from the base source under `set_option linter.deprecated false in`, inside the stage's certificate file.

Recommended use (D4):

- **Certificates for every restated declaration, out of the build.** Each stage generates `S<k>Certificates.lean` in scratch (`import BeaconcryptCore`, one `vcvio_legacy_twin` per restated theorem, and one wrapper-equation certificate `W … = <old body>` per wrapper). It runs through `coord.sh lean` against the stage build, and the stage receipt records its output, the base and new dump hashes and the file hash.
- **Transitional twins in the build only where a later stage consumes the declaration.** Only 72 of the 756 restated declarations are referenced by proofs in later stages: 221 consumer declarations (229 references) in 159 consumer-file patches over the whole plan. The 72 split as S2 11, S3 2, S4 20, S5 5, S6 22, S7 5, S8 7. For these, the `vcvio_legacy_twin T` line goes right after T in T's own module (no new import, no cycle). Consumers are patched by a scripted rename of `T` to `T_vcvioLegacy`. When the consumer's own stage arrives, it switches back to `T`, and the twin line is deleted once its last consumer has moved. Twins in per-stage modules would create import cycles for 47 consumer modules (checked with the import graph), so they stay in place.
- **End state.** No twin remains. The only deprecated syntax is in `VCVioLegacyBridge` (explicit, allowlisted), which stays until the VCVio upgrade because migrated proofs that consume façade-stated VCVio lemmas (for example `binding_bound` in `VCVioFeasibility`) bridge through it. The alternative, keeping all twins in the build until the upgrade, gives continuously checked certificates at the cost of about 756 generated declarations that reference deprecated constants.

### 5.3 Published names cited by docs, receipts and the inventory

Citation counts for the restated set (756) and the wrapper-reached set (680) are in `plan/data/cited.json` and `plan/restated-declarations.tsv`.

| Citing source | Restated declarations (statement changes, certified) | Wrapper-reached declarations (exact statement kept) | Policy |
| --- | --- | --- | --- |
| `beaconcrypt-core/proofs/check-inventory.sh` (`#print axioms` pins, `^theorem NAME` pins, per-module theorem and guard counts) | 421 | 518 | Names, guard lines and per-module counts stay valid by construction: no renames, no added `theorem` lines in existing modules, and twins are command lines. New shim modules add manifest rows, raise the `handwritten-lean` count (1982 + 5) and get their own name pins (D11). |
| Maintained docs (`doc/formal-verification-analysis.md` 45, `beaconcrypt-core/proofs/trusted-boundary.md` 8, `doc/composition-assumptions.md` 2, `doc/formal-verification.md` 2, the Lean README 1, `doc/ctx-commitment.md` 1; 46 distinct declarations) | 46 | 370 | Names are unchanged, so references stay valid. Doc lines that quote a restated statement in the old notation are updated in the same stage. The lines quoting the old notation today are 14 in the analysis document, 5 in the README, 4 in `ctx-commitment.md` and 2 in the trust boundary, plus LA-09 and the toolchain summary there (S9). |
| Proof receipts `doc/impl/proof-receipts/*.json` (historical) | 23 | 206 | Never edited (historical records under AGENTS.md). Their hashes stay true for their basis commits. The migration's own receipts list every cited declaration with its certificate result. |

The declarations that must keep their exact elaborated statements are therefore all declarations outside the restated set. That includes every wrapper-reached headline statement, among them `PqxdhDeployment*` (352) and the 122 statements over `PqxdhJointIdentity.advantage`, and gate G4 enforces it by type hash. The restated declarations cannot keep the deprecated form under a zero-warning goal. They keep their names, guards and exact meaning, proven by the hash-checked iff certificate. These include headline restated theorems cited in several documents, such as:

- `PqxdhHeadlineBridges.authenticated_native_root_bound_bridged`;
- `PqxdhOpenBridges.authenticated_native_root_bound_bridged_open`;
- `PqxdhReceiveHeadlineBridges.authenticated_extracted_root_bound_receive`;
- `PqxdhServerAuthCollision.collB_probability`;
- `RawCtxSelectedKeyProbes.candidate_bound`.

If the owner wants some of these to keep their literal old statements permanently, that needs suppressed deprecated syntax in their modules (not recommended; D4).

## 6. Hash-pinned and generated files

| File | Pin | Uses | Policy |
| --- | --- | --- | --- |
| `Computational/PqxdhJointIdentity.lean` | `beaconcrypt-core/proofs/source/getter-profile.py` `SOURCE_SHA256` (a review tripwire; the checker reads no facts from the file) | one site: the body of wrapper `advantage` (line 118); 122 statements use the wrapper | Recommended (D5): edit in S4, update the digest in `getter-profile.py`, run `test-getter-profile.py`, run `coord.sh inv rehash` for both files, and record the change as a reviewed trust-boundary item. Alternative: leave it untouched as the single documented warning, and keep `advantage` in the deprecated form. |
| The other 6 Lean files pinned by `getter-profile.py`, the 5 Lean files pinned by `check-exact-far.py`, `Model/**` (aggregate `IDEAL_MODEL_DIGEST` of `scripts/check_lean_panic_freedom.py`) | SHA-256 | none; the reference probe also shows that none of them references any restated declaration | Never edited by this migration. |
| Generated `Extraction.lean`, `Extraction/*.lean` (including the two templates) and `PanicFreedom/API.lean` | `generated-lean` inventory rows, byte-equality render | none | Never edited or regenerated. Lane 1's 21 `nameCheck` hits in `Extraction/Funs.lean` stay as they are. |
| Control files (`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, the two overlay patches, `apply-dependency-patches.sh`, `hax.toml`, `flake.nix`/`flake.lock`) | inventory | — | Untouched. The `check-inventory.sh` line that pins VCVio `98dc1089` stays. |
| Every edited handwritten Lean file and edited control or doc file | `reviewed-inventory.txt` | — | `coord.sh inv rehash` per stage. New modules need `coord.sh inv recount` and a `check-inventory.sh` count edit, which is reviewed like any inventory change. |

## 7. Stages

Stages follow the family-level reference graph bottom-up. Counts are at central `8f81b003`, before lane 1 and before S0 moves its 29 proof-only sites (S0 takes 1 site from S3, 9 from S5, 4 from S6 and 15 from S8). "Twins" are restated declarations referenced by proofs in later stages. "Consumers" are those later declarations, and the files that hold them, which get the scripted rename. Per-file detail is in `plan/stage-files.tsv` and per-declaration detail in `plan/restated-declarations.tsv`.

| Stage | Families | Files with sites | Sites (warned / suppressed) | Restated theorems | Direct wrappers | Wrapper-reached theorems (text kept) | Suppression lines | Twins | Consumer declarations (files) | Restated cited: docs / receipts / inventory | Agent-days |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| S0 | shim and bridge modules (new); proof-only sites in 14 files | 14 | 29 (21 / 8) | 0 | 0 | 0 | 1 (before `relTriple_support`) | 0 | 0 | 0 / 0 / 0 | 3–5 |
| S1 | VCVio*, CtxReduction*, CtxTransition*, CtxRetained*, CtxAuth* | 5 | 22 (22 / 0) | 4 | 18 | 14 | 0 | 0 | 0 (0) | 0 / 0 / 0 | 1–2 |
| S2 | CtxRom*, LiveApplication*, PqxdhPublic*, PqxdhChallenge*, PqxdhMaterial*, JointEager*, JointTable*, RawKey*, StatefulGood*, UniformTarget*, PqxdhBoundary*, PqxdhOrdered*, PqxdhSecret* | 14 | 91 (84 / 7) | 40 | 2 | 1 | 6 | 11 | 69 (52) | 1 / 1 / 8 | 1.5–4 |
| S3 | PqxdhProjection*, PqxdhHidden*, PqxdhExtract* (three large proof files) | 3 | 232 (206 / 26) | 57 | 0 | 0 | 8 | 2 | 10 (8) | 0 / 2 / 6 | 2–4.5 |
| S4 | AdaptiveSeal*, CtxPrefix*, PqxdhFull*, PqxdhKem*, PqxdhLive*, PqxdhStateful*, CtxIndependent*, PqxdhOptional*, {PqxdhJoint*, PqxdhDynamic*, PqxdhPhase1*} | 26 | 176 (176 / 0) | 78 | 5 | 12 | 0 | 20 | 45 (34) | 8 / 1 / 19 | 2–5 |
| S5 | CtxNonce*, PqxdhKnown*, PqxdhPrivate*, AdaptiveRaw*, CtxComputational*, CtxUnclaimed*, PqxdhCorrelated*, PqxdhGenerated*, AdaptiveCtx*, PqxdhPhase2* (+ wrapper-only PqxdhAccepted*, PqxdhProtocol*, CtxHonest*) | 29 | 275 (275 / 0) | 115 | 6 | 76 | 0 | 5 | 20 (12) | 6 / 0 / 17 | 2.5–6.5 |
| S6 | RawCtx* | 58 | 359 (359 / 0) | 156 | 0 | 6 | 0 | 22 | 57 (36) | 5 / 1 / 118 | 3.5–8 |
| S7 | {PqxdhInitial*, PqxdhAuthenticated*}, PqxdhFinal* (+ proof-term-only PqxdhInitializer*, PqxdhComposition*, PqxdhSelected*) | 44 | 165 (165 / 0) | 91 | 2 | 11 | 0 | 5 | 9 (7) | 9 / 0 / 75 | 2–4.5 |
| S8 | PqxdhServer*, PqxdhFirst*, PqxdhAdaptive*, PqxdhHeadline*, PqxdhHypothesis* | 43 | 287 (36 / 251) | 125 | 3 | 78 | 117 | 7 | 11 (10) | 5 / 1 / 124 | 2.5–6.5 |
| S9 | PqxdhRecord*, PqxdhRegistration*, PqxdhRoot*, PqxdhOpen*, PqxdhLater*, PqxdhDeployment*, PqxdhReceive*; final sweep | 24 | 146 (36 / 110) | 54 | 0 | 417 | 52 | 0 | 0 (0) | 12 / 17 / 54 | 2.5–4.5 |
| Total S1–S9 (S0's sites are a subset) | | 246 | 1753 (1359 / 394) | 720 | 36 | 615 | 183 | 72 | 221 | 46 / 23 / 421 | 20–46 (23–51 with S0) |

Stage notes:

- **S0 (shim, bridge, tooling, proof-only fixes).**
  - Re-baseline on post-lane-1 central (section 8, step 1).
  - Build the tooling in scratch: a pin-filtered codemod wrapper around a copy of upstream `scripts/migrate-native-probability.py`, keeping the notation, `𝒮`-equation and `GameEquiv` rewrites and the 7 RENAMES whose target exists at the pin, plus the 16 whose target the shim backports. The wrapper disables the MODULES remaps, the removed-namespace deletions and the `IsUniformSpec` binder rewrites, which only make sense upstream. Also the gate scripts G1 to G6, the twin-rename script driven by the reference probe, and the certificate generator.
  - Add the five modules and their forward replay check.
  - Make the 29 proof-only replacements.
  - Inventory and registry: five new modules, root imports, manifest rows, count, name pins.
  - Docs: a plain-English note on the shim, the bridge and the policies, and a trust-boundary note that the backports are project-proved, not trusted.
  - No statement changes.
- **S1 (pilot).**
  - Covers all three replacement shapes: wrapper bodies (18 advantages and probabilities over Bool and over concrete attempt types without instances), `probEvent` statements over concrete types without instances (`VCVioFeasibility`), and a VCVio façade-stated dependency (`binding_bound`, consumed through `vcvio_legacy`).
  - No cross-stage consumers.
  - `CtxReduction`, `CtxTransitionReduction` and `VCVioFeasibility` are canonical root imports with inventory theorem pins, which tests the inventory path.
  - The README paragraph on the VCVio pilot is updated.
- **S2 (leaf families).** The largest frontier relative to its size (69 consumer declarations in 52 files, from `PqxdhSecretInputKdf`, `UniformTargetSelection` and `CtxRomAuth`), so it exercises the twin and rename tooling. Includes 6 suppression lines.
- **S3 (three large proof files).** 135 proof sites, mostly `𝒮`/`evalSPMF` algebra in `PqxdhProjectionCollisions` (141 sites) and `PqxdhHiddenRoot` (65). `PqxdhExtractRomHiddenSuffix` is fully suppressed today (26 sites). Expect manual work on `𝒮` shapes outside equations.
- **S4.**
  - Contains the two widely used wrappers: `PqxdhJointIdentity.advantage` (pinned file, D5) and `PqxdhOptionalKemSource.HonestKeyCompatibility`, whose `𝒮` body over `Option (MlKem768Ciphertext × MlKemSharedSecret)` becomes an `=ᵈ` statement.
  - Their 193 type-level users in later stages keep their text.
  - 20 twins serve 45 consumer declarations in 34 later-stage files.
- **S5.** The CTX nonce/AEAD and computational CTX families, with 9 of the 15 Boolean-bound sites already handled in S0, plus the adaptive raw/CTX families.
- **S6.** `RawCtx*`, 58 repetitive files, 118 inventory-pinned restated theorems. Best split between two agents along the internal import order.
- **S7.** Initial and authenticated root families, including the restated authenticated-root bounds cited in the analysis document.
- **S8.**
  - All 216 `PqxdhServer*` sites are suppressed today (117 suppression lines, two of them file-wide: `PqxdhServerAuthPublicationCaptureHistory` and `PqxdhServerAuthPublicationMarkedHistory`). Removing the suppression is part of the stage, and it may also surface hidden non-VCVio deprecations.
  - Also contains the headline bridges.
- **S9 and the final sweep.**
  - Record lift, registration (three file-wide suppressions in `PqxdhRegistrationJointKem{Commands,Initialization,Routing}`), deployment (352 wrapper-reached headline statements whose text is unchanged) and the open/receive bridges.
  - Final sweep:
    - delete the remaining twin lines (none should remain);
    - run the final acceptance check (section 9) on the whole project;
    - update trusted-boundary LA-09 and the summary at line 489, which still say "discrete `evalSPMF`" (a trust-boundary documentation change, no change of trust), and the Lean README;
    - write the residual report for the upgrade (section 14).

## 8. Per-stage procedure and exit criteria

1. **Base and workspace.**
   - Start from central after the previous stage landed. Register the branch (for example `codex/vcvio-deprecations-s<k>`), the clone or worktree and any scratch directory first.
   - Copy `.lake` read-only from a registered source (never from or into `/home/user/bc-hax`). Use the two-file flake directory with central's `flake.nix`/`flake.lock`.
   - Re-run the usage scan (`usage/scripts/scan_sources.py`), the usage probe and the reference probe (`plan/ProbePlan.lean`) against the base's published LEAN_PATH. Recompute the stage's file, restated, twin and consumer lists, and take the base declaration dump.
2. **Edit.**
   - Run the pin-filtered codemod on the stage files.
   - Delete their `set_option linter.deprecated false` lines.
   - Fix the remaining errors bottom-up within the stage. Use single-file checks through `coord.sh lean` after `lake build` of the dependencies under `coord.sh lease mem claude @lake …`.
   - Add the `vcvio_legacy_twin` lines for the stage's twins, and run the rename script on their consumers in later stages.
   - Switch this stage's own consumer references from earlier twins back to the original names, and delete earlier twin lines that no longer have a consumer.
3. **Build.** Run `make check-lean` (policy, root, panic-freedom and `lake --rehash build`) in the proof shell with `SHELL=bash`, under `coord.sh lease mem claude @lake <label> -- …`.
4. **Gates.** Run G1 to G6 of section 9 and the stage certificate file through `coord.sh lean`. Run `coord.sh inv rehash` (and `inv recount` if modules were added), then `check-inventory`.
5. **Docs.**
   - Add a plain-English paragraph for the stage in `doc/formal-verification-analysis.md`: what was restated, why each new statement is equivalent, the certificate counts and the residual.
   - Update the maintained doc lines that quote a restated statement.
   - Write the receipt `doc/impl/proof-receipts/vcvio-deprecations-s<k>.json`: commits, gate outputs, certificate output, dump hashes and tool hashes.
6. **Review.** Two independent reviewers. One checks statement fidelity (G4 diff, certificate log, binder lists, guard messages). The other checks hygiene (forbidden names and patterns of section 3, residual growth, docs, inventory).
7. **Validate and land.**
   - Run `coord.sh pvmatrix claude @pvmatrix vcvio-deprecations-s<k> --eta 6h -- make verify-in-shell` (cadence: D7).
   - Commit with the exact `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>` footer, and push after each milestone (no amend, rebase or force-push).
   - Integrate on central under `coord.sh lease integration`, then publish the new LEAN_PATH for the next stage.

A stage is landable when all of the following hold:

- the full build passes;
- G1 to G4 pass for the stage, and G5 introduces no forbidden name;
- `check-inventory` passes;
- `verify-in-shell` passes, or is deferred to a milestone under D7;
- the project-wide VCVio deprecation warning count has dropped by exactly the stage's warned sites;
- every consumer outside the stage builds.

## 9. Checks (gates) and the final acceptance check

| Gate | What it checks | Tool | Per stage | Final |
| --- | --- | --- | --- | --- |
| G1 deprecation warnings | `has been deprecated` warnings in `BeaconcryptCore` files of the full build log whose constant is one of the 41 deprecated VCVio/ToMathlib/PolyFun declarations (usage `deprecated_declarations`) | `usage/scripts/parse_log.py` on the `make check-lean` log | 0 in stage files; global count = previous − stage warned sites | 0 project-wide |
| G2 source sites and suppression | lexer scan for the 41 names and the notations `Pr[`, `Pr[=`, `Pr[⊥`, `𝒮[`, including sites under suppression; every `set_option linter.deprecated false` | `usage/scripts/scan_sources.py` | 0 sites and 0 suppression lines in stage files | 0 outside `VCVioLegacyBridge` |
| G3 elaborated statements | project declarations whose type or definition body references `probOutput`, `probEvent`, `probFailure`, `evalSPMF` or the Boolean lemma (any SPMF reference left comes through VCVio program-logic definitions and is reported) | `usage/scripts/ProbeUsage.lean` | 0 in stage modules except twins `*_vcvioLegacy` | 0 outside `VCVioLegacyBridge` |
| G4 statement fidelity | declaration dump before and after: no removed or renamed declaration; type-hash changes ⊆ stage allowlist; def-value changes ⊆ stage wrappers; one passing iff certificate per allowlisted declaration (hash and `pp.all` equality with the base); wrapper-reached statements unchanged | lane 1 `declcheck/DeclsAll_*.lean` + `scripts/decl_compare.py`; `S<k>Certificates.lean` | pass | cumulative dump from the plan's base to the end: changes = union of stage allowlists, all certified |
| G5 forward names | VCVio-package constants referenced by project types and definition bodies (outside the bridge and twins) exist at afa6593f with an unchanged type hash or a recorded source-compatible change (from `api/outB/all-pkg-consts.jsonl`, refreshed if a newer target is chosen); no forbidden name of section 3 in stage modules; backport replay against the upstream build; residual report of façade-layer constants removed upstream that proofs still reference (baseline 2807 file × constant pairs, 2806 of them in stage modules: S1 27, S2 126, S3 96, S4 196, S5 375, S6 407, S7 352, S8 505, S9 722) | `api/ProbeUsed.lean` re-run + join; forward replay file | no new forbidden name; residual of stage modules not above its baseline | all statements and definition bodies clean; residual listed for the upgrade |
| G6 repository checks | `make check-lean`, `check-inventory`, `test-getter-profile.py` when `PqxdhJointIdentity` changes, all `#guard_msgs` axiom guards within `propext`, `Classical.choice`, `Quot.sound`; full `verify-in-shell` | Makefile, `coord.sh pvmatrix` | pass | pass |

The final acceptance check is G1 to G6 on the whole project at the end of S9. Its result is "zero VCVio deprecation warnings, zero deprecated syntax outside the one allowlisted bridge module, zero deprecated constants in statements and definition bodies outside it, every VCVio name in statements and definitions present upstream with a compatible statement, and every backport replayed against upstream".

G5 measures names at the level of statements and definitions. Names used inside proofs that are removed upstream are reported, not gated. They are the remaining upgrade work, and driving them to zero is the optional phase B (D6).

## 10. Risks

| Risk | Effect | Mitigation |
| --- | --- | --- |
| Lane 1 not yet on central (`c1b6e475`, 295 files changed) | conflicts; stale line numbers | start after lane 1 lands; re-baseline in S0 step 1 |
| Certificates do not reproduce the old type exactly (instance paths, universe instantiation) | hash mismatch | `pp.all` comparison; textual twin fallback; review |
| `Pr{…}` elaborates differently upstream (U6), and the pin's simp bridges hide this (C6a, U7) | proofs pass at the pin and break at the upgrade | rules of section 3; G5 residual; reviewer checklist with a grep for `change`/`show` through `𝒟[do`, `{True}` and the three simp bridges |
| Backport statements drift from upstream, or upstream moves again (Lean 4.35 #866; #821 "interpret events through core WP and retire SPMF" is a ready PR) | backports or the vocabulary need another pass | forward replay check per stage; G5 parameterized by the target's constant dump; re-run against the newest tag when it exists |
| Frontier churn: 221 consumer declarations patched and later restored | review noise, merge conflicts | scripted rename from the reference probe; twins live in the defining module; the bottom-up order keeps every consumer in a later stage (0 ordering violations) |
| `𝒮` shapes the codemod cannot rewrite (68 in 28 files) and the 545 proof sites | effort variance | estimated as manual work; pilot recalibration |
| Removing 183 suppression lines surfaces other hidden deprecations (Mathlib) | extra fixes | fixed in the same stage; lane 1's rename table applies |
| Full rebuilds after low-level edits (about 25 minutes each) and `verify-in-shell` (about 5.5 hours) | calendar time | batch fixes per build; D7 cadence; at most 2 or 3 heavy agents at a time |
| `relTriple_prod` import pulls `FromUnary`, `StdDoBridge` and `WriterTBridge` into the closure | small build growth; axiom closure must stay clean | the project's axiom guards check every printed closure; `FromUnary` exists upstream too |
| The 10 `OracleComp` applications (VCVio-feasibility cache games, `CtxRO`, `spec'`) need bridge lemmas beyond `ProbComp` | bridge gaps | bridges stated monad-generically with the pin's `DiscreteEvalDistCompatible`; checked in S0 and S1 |
| Twin and backport declarations under VCVio names | name clash if the pin module defining them is ever imported, or if VCVio is bumped without deleting the shim | absence check across the whole pin package; the upgrade procedure deletes the shim bodies first (loud duplicate-declaration error otherwise) |
| Non-deprecated API that upstream also removed is not reached by following warnings: `ProbComp.boolDistAdvantage` (171 modules), `OracleSpec.QueryCache` as a function (336 files name it), discrete `tvDist` (77 files), `expectedValue` (6), KEM advantage ℝ → ℝ≥0∞ (51 modules), relational binder changes (59 files), 61 names renamed without aliases in 967fdf2e, 5 removed imported modules | the upgrade remains a separate effort after this plan | listed in the final residual report; candidate follow-on items (D8) |
| Disk: one new clone with `.lake` (about 13 GiB), and the upstream scratch build (12 GiB) must be kept for the replay checks | disk level | `coord.sh disk report` before creating; reuse lane 1's clone after it lands if the owner agrees |

## 11. Owner decisions needed

1. **D1 Edit permission.** Allow editing published (frozen) central modules for this migration (PROTOCOL: published modules are frozen; the 2026-10-19 approval covered lane 1 only), and allow the five new modules.
2. **D2 Vocabulary.** Use upstream's final idioms (`Pr{…}`, `=ᵈ`) wherever they differ from the attribute's literal suggestion (`𝒟[mx] {x}`, `𝒟[mx] {x | p x}`, measure equations under a ⊤ σ-algebra). Recommended: yes.
3. **D3 Backport naming.** Recommended: upstream names in upstream namespaces, guarded by the absence check, so the upgrade needs no call-site edits. Alternative: a project namespace, with renames at the upgrade.
4. **D4 Certificates and the bridge.** Recommended:
   - out-of-build, hash-checked iff certificates for every restated declaration, recorded in stage receipts;
   - in-build transitional twins only for the 72 cross-stage-consumed declarations, all removed by the end;
   - one allowlisted bridge module with explicit suppression, kept until the VCVio upgrade.

   Alternatives: keep all twins in the build until the upgrade, or keep literal old statements for selected headline theorems (not recommended).
5. **D5 Pinned file.** Recommended: edit `PqxdhJointIdentity.lean` in S4 and update the `getter-profile.py` digest. Alternative: one documented permanent warning.
6. **D6 Proof scope.** Recommended for this plan: gate statements and definitions, and report the proof residual. Optional phase B: drive the façade-lemma residual in proofs to zero outside the bridge, about 10 to 20 extra agent-days, best done opportunistically while each stage's files are open.
7. **D7 Validation cadence.** Recommended: full `verify-in-shell` through `pvmatrix` for every landing on central. Lean-only changes cannot affect ProVerif, so a cheaper option is Lean-level checks per stage and a full verify after S3, S6 and S9.
8. **D8 Boolean bound and `boolDistAdvantage`.** Recommended: follow the warning literally behind one shim lemma, and leave the non-deprecated `ProbComp.boolDistAdvantage` family (removed upstream on 2026-09-25) for a separate item.
9. **D9 New VCVio import.** Add `VCVio.ProgramLogic.Relational.FromUnary` for `relTriple_prod`. Recommended: yes.
10. **D10 Documentation.** Update the maintained documents that quote restated statements in each stage, and the trust boundary (LA-09, summary) in S9, as documentation changes without a change of trust.
11. **D11 Inventory.** Pin the shim and backport names and counts in `check-inventory.sh` (recommended), and accept the `handwritten-lean` count change.

## 12. Effort

The estimates assume the S0 tooling. Per agent-hour they count:

- 0.10 to 0.25 per restated theorem;
- 0.04 to 0.10 per proof site;
- 0.2 to 0.5 per wrapper;
- 0.05 to 0.15 per consumer patch;
- 4 to 8 fixed hours per stage for setup, gates, inventory, docs, receipts and two reviews.

They do not count machine time.

| Stage | S0 | S1 | S2 | S3 | S4 | S5 | S6 | S7 | S8 | S9 | Total |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Agent-days | 3–5 | 1–2 | 1.5–4 | 2–4.5 | 2–5 | 2.5–6.5 | 3.5–8 | 2–4.5 | 2.5–6.5 | 2.5–4.5 | 23–51 |

Machine time per stage is four or five full Lean builds (about 25 minutes each), the probes and certificate runs (under 10 minutes), and `verify-in-shell` (about 5.5 hours, unattended). Two agents can split the larger stages (S5, S6, S8) by internal import order, within the protocol's limit of two or three heavy agents. The pilot (S1) measures the real cost per theorem, site and consumer, and the remaining estimates are rescaled at the go/no-go review.

## 13. Recommended first increment

Increment 1 is S0 plus S1, landed on central as one stage after full checks, in four commits that each build:

1. **The four forward shim modules,** with the forward replay check against the afa6593f build.
2. **The `VCVioLegacyBridge` module** with the bridge lemmas, the `vcvio_legacy` simp set, the twin command and the certificate checker.
3. **Proof-only replacements, no statement change.** The 15 Boolean-bound sites go through the ProbabilityTheory shim lemma. The two private `relTriple_prod` copies (`product_coupling`, `relTriple_support`) become `relTriple_prod …` with the `FromUnary` import. This commit removes 29 sites and 21 warnings.
4. **The S1 pilot.** The 18 wrapper bodies of `CtxReduction`, `CtxTransitionReduction`, `CtxRetainedTagProjection` and `CtxAuthClassification`, and the four `VCVioFeasibility` statements. Certificates are generated for all 22 declarations; the analysis note, the README paragraph and a receipt are added.

The increment removes 51 sites and 43 warnings and changes 22 declarations, each certified. It exercises every policy of this plan: shim, backports, forward replay, certificates, wrappers, inventory pins and the façade-stated `binding_bound` dependency. Its cost is 4 to 7 agent-days.

The go/no-go review after it checks four things:

- the certificate exactness rate (target: all 22 by hash);
- that the codemod works at the pin without hand edits beyond the expected ones;
- the measured cost per item;
- the owner's answers to D2 to D7.

If the owner wants a smaller first landing, the proof-only replacements of commit 3 can land alone first (about 1 agent-day), using the attribute's replacement `ProbComp.evalDist_apply_true_le_add_ofReal_boolDistAdvantage` inline instead of the shim lemma.

## 14. What remains for the actual upgrade (outside this plan)

After S9, moving to upstream VCVio (afa6593f today, or the next tag) needs:

- the two manifest revisions;
- deleting the shim bodies and `VCVioLegacyBridge` with its `vcvio_legacy` uses;
- the reported proof residual (G5);
- the non-deprecated removed API listed in section 10;
- the control-file, inventory and trust-boundary updates of `stack.md` section 5.

Statement text written in this plan's vocabulary is expected to stay unchanged, because `Pr{…}`, `=ᵈ`, `𝒟[…]` and the backported names have the same source form upstream (checks U1 to U5 and the replay check).

## 15. Evidence and files

- `/tmp/bc-arc-scratch/vcvio-survey/plan.md`: this plan.
- `/tmp/bc-arc-scratch/vcvio-survey/plan/` (registered scratch):
  - `ProbePlan.lean` and `run-probe.sh`: reference and monad probe, run once through `coord.sh lean` against the published LEAN_PATH of `8f81b003` (21 s);
  - `probe-out/edges.tsv`, `probe-out/monads.tsv`: probe output;
  - `data/imports.json`: project import graph;
  - `data/cross-edges.json`, `data/levels.json`, `data/stages.json`, `data/cited.json`, `data/restated-cited-in-docs.txt`;
  - `stage-files.tsv`: 429 files with any work, by stage;
  - `restated-declarations.tsv`: 756 rows with stage, citations and cross-stage consumers;
  - `py/`: the generating scripts (`imports.py`, `graph.py`, `levels.py`, `stages.py`, `cited.py`, `monads.py`).
- Inputs: `/tmp/bc-arc-scratch/vcvio-survey/{pin-replacements,usage,api-map,stack}.{md,json}`, `pin/facade-replacements.json`, `api/codemod-tables.json`, `api/codemod-run/`, `api/vcvio-upstream/` (afa6593f build), and lane 1's `/tmp/bc-arc-scratch/lean-warnings/declcheck/` and `scripts/decl_compare.py`.

## Amendments

Recorded after the owner's acceptance; the plan text above is unchanged, and where it disagrees with an amendment, the amendment holds.

### A1 (Claude main thread, 2026-10-19, after the validation of stage S0): the step 7 source scan stays a zero-hit gate

Source: `/tmp/bc-arc-scratch/vcvio-migration/AMENDMENTS.md` (sha256 d4334b8880ec61e131e76294235d4670b448007d51f64d80ead0e742f7835469). The validation of stage S0 found five hits of the source scan of the completion checklist (step 7), all in new plan modules: `VCVioLegacyBridge.lean` (the tactic macro, two command syntaxes and the `addDecl` of the twin command) and `VCVioForwardEvalDist.lean` (the `infix` for `=ᵈ`). The scan keeps custom metaprogramming and global notation out of the trusted build, and it is not allowlisted. Instead:

1. `=ᵈ`: the backported `infix:50 " =ᵈ " => EvalDistEq` is removed. Statements write `EvalDistEq A B`, using the backported definition `EvalDistEq` under its upstream name and namespace (D3 unchanged). At the VCVio upgrade, the backported definition is deleted and these statements refer to upstream's `EvalDistEq` with no call-site edit. Upstream's `=ᵈ` notation comes from the VCVio dependency, which the scan does not cover. Where this plan writes `A =ᵈ B` for a statement in the build, read `EvalDistEq A B`.
2. The `vcvio_legacy_twin` command and all other certificate tooling (any macro, syntax, elaborator, `addDecl`, `run_cmd` or meta code), including the `vcvio_legacy` tactic, move out of the build into a scratch module (`/tmp/bc-arc-scratch/vcvio-migration/tools/CertTools.lean`). Only the out-of-build certificate files import it: they `import BeaconcryptCore` and the tools module and run through `coord.sh lean` with a `LEAN_PATH` that adds the tools' olean. Migrated build proofs name the bridge lemmas of `VCVioLegacyBridge` in `rw` or `simp only`.
3. In-build transitional twins (the 72 cross-stage-consumed declarations) become plain generated source text. The tool prints, for each twin, `set_option linter.deprecated false in theorem T_vcvioLegacy : <old statement text> := <bridge proof from T>`, which goes right after `T` in `T`'s module. Each twin's type is checked against the pre-stage dump by the certificate run. All twins are removed by the end (D4 unchanged).
4. The result: the source scan on every stage tree prints `hits 0`. Deprecated syntax remains only inside `VCVioLegacyBridge` (lemmas, no metaprogramming) and in the transitional twins, both under explicit `linter.deprecated false` suppression and both pinned in the inventory.

### A1.1 (Claude, 2026-10-20, S0 review fixes): the second twin header, and how G2 and the inventory treat twins

Source: `/tmp/bc-arc-scratch/vcvio-migration/AMENDMENTS.md` (sha256 5b13fa5512b4feee18a60ce066f4f089bf4bc8eed3bb428129ffad2e9b7561f1, which appends A1.1 to the unchanged A1 text). It refines A1 item 3; the S0 certificate self-test found the need, and the S0 hygiene review asked for this record. A delaborated old statement can name binders that its text never references (for example an instance binder printed as `[inst : C]`), which the build's unused-variable linter reports. For such a twin only, the tool prints the header `set_option linter.deprecated false in set_option linter.unusedVariables false in theorem _root_.T_vcvioLegacy :`; it tries the plain A1 header first and takes the second only if the twin command then produces a message. Both variants are the one-line header of one generated command; the unused-variable switch is a linter option with no effect on what is proved, and it is allowed only on twin header lines.

1. Gate G2 treats both header variants as twin headers: twin lines are exempt from the deprecated-site and suppression-line counts, are counted separately, and their set must equal the stage's twin list. (The S0 gate script recognised only the first variant and read the wrong field for the twin name; corrected on 2026-10-20 and tested on the ten self-test twins.)
2. Inventory: the first stage that inserts twins adds to `check-inventory.sh`, for each module with twins, the count of twin header lines of each variant, and a pin that `linter.unusedVariables` occurs in that module only on twin header lines; these pins are removed together with the twins. (Today `linter.unusedVariables false` occurs only in six generated or assumption files, none of them a computational module.)
3. A1 item 4 is unchanged: the deprecated syntax of a twin stays under the explicit `linter.deprecated false` suppression of its header line, and all twins are removed by the end (D4).

### A2 (Claude, 2026-10-20, S2 review fixes): statements whose forward notation has no native semantics at the pin

Source: `/tmp/bc-arc-scratch/vcvio-migration/AMENDMENTS.md` (sha256 0ec668aca2f276a2eb3a882eb80b9375d3d1095713fffacdefde4d5c050e83a9, which appends A2 to the unchanged A1 and A1.1 texts). The S2 statement-equivalence review (finding EQ-S2-1) asked for this record. Items 1 to 3 are implementation rules inside the plan and apply from S2 on. Item 4 proposes a change of the final acceptance check of section 9 and of the D6 target; it needs the owner's decision and is not in effect.

1. The class. At the pin, `Pr{…}` and `EvalDistEq` elaborate with VCVio's native free-monad semantics for `ProbComp` and for oracle computations whose answers are discretely measurable. Over an arbitrary specification with uniform answers (`[spec'.IsUniformSpec]`, as in `StatefulGoodEvent`) and over a specification whose answers carry no measurable structure (`CtxRO`, as in `CtxRomAuth.ctxFreshAliasVerifier_le_inv`), the pin's only semantics is the SPMF adapter `instEvalDistSemanticsOfMonadLiftTSPMF`, so the elaborated statement contains `SPMF` and the adapter instance. Section 3 forbids the measurable binders and global instances that would select the native semantics, so these statements keep the adapter semantics. Their certificates are unaffected, their proofs reach VCVio's laws through `VCVioLegacyBridge`, and their remaining façade uses are recorded phase B exceptions. In S2 the class is `StatefulGoodEvent.event_good`, `output_good`, `output_bad_zero`, `output_good_false` and `CtxRomAuth.ctxFreshAliasVerifier_le_inv`. Upstream has a single native semantics of oracle computations, so the class is residual for the upgrade (section 14).
2. Gate report. From S2 on, G3 also reports, without a pass criterion, the declarations whose type or definition body references `SPMF` but no deprecated statement head, with the new ones of the stage and those whose type references the adapter instance. In S2 the count goes from 108 to 113; the five new ones are the class of item 1, all with the adapter instance in their types, and the 108 at the base use the non-deprecated SPMF-valued API (`tvDist`, expectations, `boolDistAdvantage`) that section 10 leaves for the upgrade.
3. Later consumers. The four later-stage consumers of `StatefulGoodEvent.event_good` (`RawCtxFlaggedQueryAgreement`, `RawCtxSelectedParentLive` and `RawCtxSelectedLiveEvents` in S6, `PqxdhRecordFactsOriginMuteAdaptive` in S9) use it for `ProbComp`; once restated, their statements elaborate natively, and `event_good` applies to them only through the bridge (two bridge lemmas each way, only the three standard axioms). Before S6 switches them back from the twin, S6 chooses between one pin-only bridge theorem in `VCVioLegacyBridge` that equates the adapter and the native reading for specifications with discretely measurable answers (guarded and pinned like the other bridge theorems) and recorded phase B exceptions for the double-bridged proofs. Neither changes a consumer's statement.
4. Pending the owner's decision, not in effect. The final acceptance check ("zero deprecated constants in statements and definition bodies outside" the bridge) and D6's final sweep (façade uses in proofs driven to zero outside the bridge) cannot hold at the pin for the class of item 1 without weakening a statement or adding an instance binder, both forbidden; read literally, the acceptance check would also fail on the 108 base declarations of item 2, although G3's own definition only reports `SPMF` references. Proposed: the final acceptance check counts the deprecated statement heads and lists, by name with the reason, the statements that reference `SPMF` only through the non-deprecated SPMF-valued API or the pin's adapter; D6's target is zero façade uses outside the bridge apart from recorded exceptions whose dependency or semantics exists at the pin only in the deprecated form (this class, and façade-stated VCVio dependencies such as `binding_bound`, which section 5.2 already lets migrated proofs reach through the bridge). Both residuals move to the VCVio upgrade.

### Revision of D7 (owner, 2026-10-19, `decision-2026-10-19.txt` item 5)

No full `verify-in-shell` runs during the VCVio deprecation migration. The migration changes only Lean files; the ProVerif models, the Rust code and the extraction inputs cannot change, and ProVerif dominates the runtime of `verify-in-shell`. Each stage is validated by `make check-lean` (dependency patches, policy, root, panic freedom, full Lake build), `make check-inventory`, the step 7 scans of the completion checklist and the stage certificates.

<!-- SPDX-License-Identifier: 0BSD -->

# VCVio feasibility for beaconcrypt computational proofs

## Decision

VCVio is feasible for beaconcrypt's current finite, classical game-based proof suite and is a better integration fit for the `lean` branch than adding a second proof assistant. It can plausibly reproduce every accepted theorem family on the tracked `ssprove` branch. The compile-checked pilot touches two necessary architectural seams without claiming full parity: a generic bounded adaptive random-oracle probability bound over production-shaped extracted types and basic linked state-handler behavior for a hidden consuming key store.

That conclusion is deliberately narrower than “VCVio replaces SSProve.” VCVio does not currently provide a drop-in equivalent of SSProve 0.2.4's complete typed package/validity layer, heterogeneous location heap, or mature package-algebra surface. Matching the repository's accepted one-call result-and-final-heap certificate is credible but requires a beaconcrypt-specific state facade and new proofs; matching arbitrary repeated contexts remains a separate step that neither current suite has completed. Neither the present SSProve suite nor VCVio supplies the full multi-session, active, extraction-linked end-to-end proof specified in [`computational-security-proof-plan.md`](computational-security-proof-plan.md), and VCVio has no quantum random-oracle or QPT adversary model.

Recommendation: use VCVio for the next computational-proof pilot if the accepted scope is bounded classical adversaries and the project is willing to implement a small local state-separated protocol layer. Do not retire the SSProve work or claim parity until the exact one-call result-and-final-state certificate, the CTX privacy hop, a two-call contextual CKEY test, and an assumption/dependency audit all pass.

## Reproducible baseline

The investigation was performed on branch `vcvio` in worktree `/tmp/beaconcrypt-vcvio`. Before creating it, `origin/lean` was fetched and the local `lean` branch was checked against it: both resolve to `7a1cf8dae26e7bd306addc8ba279d0200d1bef18`, with divergence `0 0`. The existing `ssprove` worktree and its unrelated local changes were not modified. During the final review, `ssprove` and `origin/ssprove` both advanced to `926983273ae5ff7bcd302631fb743844a6d44290`; the comparison below includes that commit's accepted package-semantics certificate.

VCVio is pinned by immutable commit `cbd4144b51d92da00dd50f05e068b2348fa6e529`, the commit behind its `v4.31.0` tag and therefore compatible with this project's Lean/Mathlib 4.31 line. The checked-in Lake manifest also locks VCVio's inherited `PolyFun` and `loom2` dependencies. The authoritative upstream descriptions are the [VCVio repository](https://github.com/Verified-zkEVM/VCVio/tree/cbd4144b51d92da00dd50f05e068b2348fa6e529), which documents `OracleComp`, denotational probability semantics, oracle simulation, logging/caching, and its proof logics, and the [VCVio paper](https://eprint.iacr.org/2024/1819), which presents the oracle representation, forking lemma, Fiat-Shamir proof, and Schnorr-like case study.

The comparison uses three distinct targets:

- Target A is the accepted repository-owned surface at tracked `ssprove` commit `926983273ae5ff7bcd302631fb743844a6d44290`: thirteen proof modules covering bounded ROM infrastructure, CTX binding and privacy, finite PQXDH/ratchet games and hybrids, one-step forward secrecy, record integrity, one state-separated composition slice, and an exact restricted one-call result-and-final-heap certificate with public-view probability and advantage equality.
- Target B is the SSProve 0.2.4 framework surface itself: valid typed packages over locations and interfaces, general discrete subdistributions, heterogeneous heap semantics, sequential and parallel composition, identities and interchange, contextual advantage/reduction laws, and pRHL. These facilities are described in the versioned [SSProve guide](https://github.com/SSProve/ssprove/blob/v0.2.4/DOC.md) and the [SSProve paper](https://eprint.iacr.org/2021/397.pdf).
- Target C is the full multi-session, active, primitive-composed, extraction-linked milestone in the repository's computational-security plan rather than either framework's library surface.

The answer is “credible match after a local state-certificate layer” for Target A, “partial, not drop-in” for Target B, and “not yet achieved by either implementation” for Target C.

## Compile-checked pilot

[`VCVioFeasibility.lean`](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/VCVioFeasibility.lean) is imported by the maintained Lean root and contains no `sorry`, `admit`, local `axiom`, or `sorryAx` dependency.

The collision-layer portion instantiates VCVio's generic adaptive lazy-ROM commitment binding theorems with `Aeneas.Std.Array Aeneas.Std.U8 229#usize`, exactly the byte-field type in the Aeneas-extracted `commitment.CommitmentTranscript`, and `BitVec 512`, the production digest width. A checked injection from Aeneas `U8` into `BitVec 8` lets Mathlib's existing fixed-vector instance supply the required finite-type evidence. For any generic binding adversary with query budget `q` and `Unit` salt, `ctx_binding_bound_tight_512` checks VCVio's tight `(q(q - 1) + 2) / (2 · 2^512)` bound, while `ctx_binding_bound_512` also preserves the looser `(q + 2)(q + 1) / (2 · 2^512)` collision-resistance-chain route with the generic verifier's two opening queries made explicit. These are useful numerical ROM results, but they are not yet a strengthening or port of `CtxGame.v` because no checked theorem embeds beaconcrypt's payload, two explanations, distinctness predicate, and verification path into VCVio's `bindingGame`.

The two approaches therefore have different remaining CTX bridges. The accepted SSProve finite game already proves that its semantic distinct-double-opening event yields an explicit unequal-input/equal-output collision witness, while its correspondence to the production/extracted 229-byte transcript remains external. The VCVio pilot still needs both an actual beaconcrypt-game-to-generic-binding embedding and the production/extraction correspondence, whether the latter reuses the existing F* transcript-injectivity/collision-witness contract or ports it to Lean. The pilot also treats the 512-bit function as an ideal random oracle; it is not a standard-model BLAKE2b collision-resistance reduction and does not prove transformed-AEAD privacy or ordinary integrity.

The state portion defines a dependent private CKEY oracle with typed `put` and `take` results, an affine `empty/full/taken` store, and a public handler linked sequentially around the private provider. Four exact theorems check successful transfer and tombstoning, a call from an assumed tombstoned state, two sequential calls returning the value at most once, and the public observation after private state is discarded. This demonstrates basic `link`/`runState` behavior, but it does not yet match the accepted SSProve certificate: its hard-coded `Bool` key, one slot, and one `Unit` public operation omit authentication/provenance, role/session checks, paired sibling bodies, the joint sampler, false-provenance early return, the complete two-location observation-and-final-heap normal form, finite-source probability/advantage equality, full lifecycle history, and arbitrary contexts. Discarding state with `run` is definitional here and is not a contextual noninterference theorem.

`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for the four probability-bound theorems and the extracted-constant theorem, and no axioms for the four exact state theorems. In particular, the imported proof path does not report `sorryAx`. The pinned VCVio tree does contain unrelated admitted modules, so this is a result for the pilot's theorem dependency closure, not a complete audit of every upstream module, `unsafe` declaration, or build option.

The accepted SSProve gate has a different reviewed trust policy: Rocq 9.0.0 and SSProve 0.2.4 are pinned, `coqchk` runs, proof-bypass syntax is rejected, and probabilistic modules are allowed exactly `boolp.propositional_extensionality`, `boolp.functional_extensionality_dep`, `boolp.constructive_indefinite_description`, and abstract real numbers `R`. The package-semantics proof deliberately avoids stock `Pr`, `Pr_op`, generic advantage, package-validity, and interchange routes whose dependency closure reaches the rejected infinite-sum interchange principle. VCVio parity therefore requires a documented no-stronger trust policy, not identical axiom names across Lean and Rocq.

## Surface comparison

| Capability | Tracked beaconcrypt SSProve use | VCVio v4.31.0 assessment |
| --- | --- | --- |
| Finite randomized games and event probabilities | All accepted probabilistic capstones use finite sources and direct event probabilities. | Match for this finite layer. `OracleComp`/`ProbComp`, `evalDist`, event probabilities, monotonicity, and finite uniform sampling cover it directly. |
| Adaptive bounded random oracles | `BoundedRom.v` supplies explicit fuel exhaustion as `None`, a hidden finite table, chronological traces, exact count/consistency facts, and witness/extractor reductions. | Likely match after an exact semantic ledger. VCVio has random-oracle implementations, caching, logging, programming, pregenerated answers, and query-bound machinery, but the port must preserve observable exhaustion, trace order, and the exact query-count convention rather than merely rule overflow out. |
| CTX binding | `CtxEventReduction.v` and `CtxGame.v` convert the actual finite double-opening event to a bounded same-run explicit collision witness. | Framework route is plausible, but parity is untested. The pilot specializes a related generic binding game numerically; it lacks the beaconcrypt-game embedding and the separate production/extraction bridge. |
| CTX privacy programming | `CtxPrivacy.v` reindexes a finite table and bounds the true/real hop by a hidden-transcript query event. | Likely match. VCVio's oracle programming, logged traces, distribution equivalences, hybrids, and identical-until-bad support the same proof shape, but this specific theorem has not yet been ported. |
| PQXDH/ratchet closed games and one-hidden-input hybrids | `PqxdhRatchetGames.v`, `PqxdhRatchetRom.v`, and `PqxdhHybridSecurity.v` use finite challenges, bounded queries, and bad-input events. | Match in expressiveness. These are ordinary oracle games and reductions; the substantive work is porting definitions and preserving the exact shared-label/prefix contract, not adding framework primitives. |
| Post-erasure forward secrecy | `RatchetForwardSecrecy.v` uses a table involution and an erased-predecessor bad query. | Match in expressiveness through couplings/distribution equivalence or identical-until-bad plus trace logging. No implementation erasure theorem is gained automatically. |
| Record integrity and fresh-guess bound | `RecordIntegrity.v` and `RecordIntegrityBound.v` partition prior queries from a fresh adaptive candidate and prove a one-bit bound. | Match in expressiveness; VCVio's logged/cached oracles and probability tools are designed for this pattern. The assumed AEAD+CTX composition remains an assumption. |
| Stateful private interfaces and one-call linking | `StateSeparatedComposition.v` hides CKEY, while `StateSeparatedPackageSemantics.v` certifies the exact restricted one-call observation and final heap and proves public-view probability/advantage equality. | Partial mechanism demonstrated, full accepted certificate not yet ported. `QueryImpl.Stateful`, typed dependent queries, `link`, parallel sums, lenses, and state-separating hybrid/equivalence APIs appear sufficient for a local one-call certificate layer. |
| General SSProve package algebra and heap validity | SSProve exposes valid packages, raw packages, location sets, heterogeneous heaps, link/parallel/identity/interchange, and contextual advantage laws. | Gap. VCVio has compositional handlers but no drop-in equivalent of the complete SSProve package record, validity judgment, or all algebraic laws over one shared heap. |
| Advantage, distance, hybrids, and reductions | SSProve supplies `AdvantageE`, reduction and triangle laws, and pRHL, although the accepted package certificate avoids dependency-tainted generic routes. | Match for Target A's finite probability equalities and hybrid mathematics through total variation/advantage, distribution equivalence, hybrid chains, couplings, and program logics. The full SSProve contextual package-reduction and pRHL surface remains part of the Target B gap. |
| Conventional PPT accounting | The repository's accepted SSProve suite is query-bounded and does not establish a full PPT implementation theorem. | No regression relative to Target A, but still incomplete for the end-to-end plan. VCVio v4.31.0 has limited asymptotic/cost scaffolding, its `secureAgainst` accepts a caller-supplied `isPPT`, and its README explicitly says computational complexity is not considered. |
| Aeneas/extracted Rust connection | Direct hax-to-SSProve import was rejected; production correspondence remains a cross-prover contract. | Better architectural fit but not automatic. Co-locating Aeneas-generated production types and VCVio in one Lean kernel reduces a representation seam; semantic refinement from Rust operations to games still needs explicit theorems/contracts. |
| Kernel and dependency policy | Pinned Rocq/SSProve, `coqchk`, proof-bypass scan, exact four-item probabilistic assumption allowlist, and avoidance of rejected infinite-sum interchange paths. | Pilot closure has only the reported standard Lean axioms and no `sorryAx`; a production gate still needs a transitive admission/`unsafe`/option audit and an explicit accepted Lean assumption policy. |
| Quantum adversaries or QROM | The accepted SSProve suite models only classical oracle queries, including its “passive quantum” capability case. | No match for genuine QPT/QROM because VCVio has no superposition-query semantics. Post-quantum primitive libraries do not change that adversary model. |

## Module-by-module parity judgment

| SSProve module | Likely VCVio route | Risk |
| --- | --- | --- |
| `ProtocolLabels.v` | Lean finite encodings and injectivity lemmas, reusing extracted constants where representations align. | Low; equality to production arrays still needs a checked bridge. |
| `BoundedRom.v` | Map its fuel, `None` exhaustion, hidden table, chronological trace, exact count/consistency, and witness/extractor rules onto VCVio random-oracle, logging, caching, and query-bound implementations. | Low-to-medium; VCVio has the primitives, but observable exhaustion and trace conventions need checked preservation. |
| `CtxEventReduction.v`, `CtxGame.v` | Define the actual beaconcrypt double-opening game, prove its event embeds in or is equivalent to VCVio's generic binding game, then connect the explicit witness to production. The pilot checks only the related production-width numeric specialization. | Medium because both the game embedding and production/extraction bridge remain open. |
| `CtxPrivacy.v` | Program the hidden transcript entry and prove identical-until-bad/distribution equivalence outside the logged bad query. | Medium; this is the most important missing pilot theorem. |
| `PqxdhRatchetGames.v` | Direct finite `OracleComp` game definitions and exact challenge-independence/equality proofs. | Low-to-medium. |
| `PqxdhRatchetRom.v`, `PqxdhHybridSecurity.v` | Logged adaptive ROMs and bad-input event reductions over the ordered five-contribution root input. | Medium; exact joint HKDF labels, lengths, and prefix behavior must remain one interface. |
| `RatchetForwardSecrecy.v` | Table programming/coupling at the erased predecessor input with a logged bad event. | Medium. |
| `RecordIntegrity.v`, `RecordIntegrityBound.v` | Logged verification queries, fresh-input partition, and uniform-guess bound. | Medium; the combined authenticator assumption is unchanged. |
| `StateSeparatedComposition.v`, `StateSeparatedPackageSemantics.v` | First reproduce the complete two-slot one-call observation-and-final-heap normal forms and public-view probability/advantage equality, then add a second-call/context-indexed theorem. | Medium-high; this is where lack of a full SSProve package/heap layer creates new local infrastructure. |

## What parity would and would not mean

Parity with the tracked SSProve branch means reproducing its finite theorem statements or strictly stronger statements under no stronger cryptographic or foundational assumptions, including the restricted linked one-call full result-and-final-heap certificate and its public-view probability/advantage equality, with matching observations and query conventions. Because Lean and Rocq have different foundations, matching assumption reports means satisfying an explicitly reviewed no-stronger policy, not matching identifier strings. Parity does not mean completing the much larger plan's arbitrary concurrent schedules, adaptive corruptions, faithful wire/parser model, exact primitive games, multi-user lifting, extraction correspondence, or full registration-and-record composition. Those remain protocol-modeling and reduction tasks regardless of framework.

The same-kernel Aeneas/VCVio arrangement reduces one representation seam because a Lean theorem can mention the extracted `commitment.CommitmentTranscript` directly. It does not establish semantic game correspondence or discharge the existing F* facts automatically. Until CTX injectivity and the collision-witness theorem are ported to Lean, a final VCVio theorem still needs a reviewed cross-prover contract just as the SSProve design did.

The current pilot imports VCVio's generic binding result from an upstream example module. A production proof should move the required generic lemma into a narrowly audited dependency path or reproduce the short instantiation locally, then freeze `#print axioms` output and audit transitive admissions, `unsafe` declarations, and relevant options. The exact SHA pin is essential because VCVio's API and active development have moved beyond the 4.31-compatible release.

## Acceptance path

1. Port `CtxGame.v` and `CtxPrivacy.v` first, using repository-owned game definitions over the extracted 229-byte transcript type; prove the actual CTX win-event embedding before applying the generic binding result, retain the explicit `q + 2` accounting, and compare theorem assumptions and bounds against SSProve.
2. Replace the example-module import with a narrow audited generic VCVio import or local theorem, add frozen `#print axioms` reports, and audit the transitive modules used by the proof root for admissions and unsafe declarations.
3. Expand CKEY to the two-slot role/session model and first prove exact one-call full observation-and-final-state plus finite-source probability/advantage parity with `StateSeparatedPackageSemantics.v`; then prove a deliberately adversarial two-call contextual theorem. Include overwrite, retake, wrong-role, wrong-session, failed construction, dropped response, and final hidden-state cases.
4. Port one representative bad-query hybrid (`PqxdhRatchetRom.v`) and one table-coupling/involution proof (`RatchetForwardSecrecy.v`). This tests the proof ergonomics that the binding pilot alone cannot measure.
5. Define a parity ledger listing each SSProve capstone, its VCVio replacement, exact observation type, query budget, numerical loss, assumptions, and whether it refers directly to Aeneas output or to a cross-prover contract.
6. Only after those gates pass, decide whether to port the remaining finite suite. Keep SSProve as comparison evidence until every accepted capstone and negative control has a checked VCVio counterpart.

The stop conditions are equally important: retain SSProve or reassess if the CTX privacy programming hop needs materially stronger assumptions, if the two-call CKEY context exposes a handler-composition gap, if the imported dependency closure cannot be kept admission-free, or if the project requires genuine QROM/QPT claims.

## Commands used

```text
git fetch origin lean
git rev-parse lean origin/lean
git rev-list --left-right --count lean...origin/lean
git worktree add -b vcvio /tmp/beaconcrypt-vcvio lean
cd beaconcrypt-core/proofs/lean
lake update VCVio
lake build BeaconcryptCore
```

## Validation

- `make -C beaconcrypt-core check-lean` passed and built the complete 8,976-job Lean root.
- `make -C beaconcrypt-core verify-lean` passed in the locked Nix proof environment after regenerating the no-exclusion Hax/Charon LLBC and Aeneas Lean output; the three monitored generated Lean source files remained byte-identical.
- `make -C beaconcrypt-core check-inventory` passed after the proof-root, dependency lock, renamed refinement files, new pilot, and trust-boundary changes were reviewed and fingerprinted.
- A separate `#print axioms` audit reported only `propext`, `Classical.choice`, and `Quot.sound` for the tight and collision-resistance-chain probability theorems and the extracted-constant theorem, no axioms for the four state theorems, and no `sorryAx` in the pilot theorem closure.
- The broader `make -C beaconcrypt-core verify` command reached the known stale F* path and stopped while checking newly regenerated F* from the Lean-enabling source refactor. That expected legacy-path failure is independent of VCVio; its generated F* artifacts were removed/restored, and the relevant locked Lean verification above passed.

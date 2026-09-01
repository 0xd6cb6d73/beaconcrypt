<!-- SPDX-License-Identifier: 0BSD -->

# VCVio feasibility and native Lean computational reductions

## Decision

VCVio is feasible for computational proofs over beaconcrypt's handwritten Lean ideal models and is a better integration fit for the `lean` branch than adding a second proof assistant. The current objective is not to reproduce the tracked SSProve branch theorem by theorem. It is to prove computational reductions for security events stated directly over the ideal PQXDH, CTX, and ratchet components and then connect those models to extracted production code through explicit refinement theorems.

That conclusion is deliberately narrower than “VCVio replaces SSProve.” VCVio does not provide a drop-in equivalent of SSProve 0.2.4's complete typed package/validity layer, heterogeneous location heap, or mature package-algebra surface, but matching that framework surface is no longer an acceptance condition. Neither the present SSProve suite nor VCVio supplies the full multi-session, active, extraction-linked end-to-end proof specified in [`computational-security-proof-plan.md`](computational-security-proof-plan.md), and VCVio has no quantum random-oracle or QPT adversary model.

Recommendation: continue with small, theorem-driven reductions against the current ideal Lean models. Use the model's real event and transition definitions, import the narrowest applicable VCVio hardness assumption or game library, and state every missing implementation-refinement and primitive-security premise explicitly. Retain the SSProve work as comparison evidence rather than a porting target.

## Reproducible baseline

The investigation was performed on branch `vcvio` in worktree `/tmp/beaconcrypt-vcvio`. The worktree was recreated from its previous signed feasibility commit, `origin/lean` was fetched at `3bf16a3ffdd34c964d501ff74e3e940269dc623b`, and that exact state was merged as signed commit `0957f7d`. The main worktree and its unrelated local changes were not modified. The SSProve comparison below records the earlier feasibility investigation, but it no longer defines the implementation roadmap.

VCVio is pinned by immutable commit `cbd4144b51d92da00dd50f05e068b2348fa6e529`, the commit behind its `v4.31.0` tag and therefore compatible with this project's Lean/Mathlib 4.31 line. The checked-in Lake manifest also locks VCVio's inherited `PolyFun` and `loom2` dependencies. The authoritative upstream descriptions are the [VCVio repository](https://github.com/Verified-zkEVM/VCVio/tree/cbd4144b51d92da00dd50f05e068b2348fa6e529), which documents `OracleComp`, denotational probability semantics, oracle simulation, logging/caching, and its proof logics, and the [VCVio paper](https://eprint.iacr.org/2024/1819), which presents the oracle representation, forking lemma, Fiat-Shamir proof, and Schnorr-like case study.

The comparison uses three distinct targets:

- Target A is the accepted repository-owned surface at tracked `ssprove` commit `926983273ae5ff7bcd302631fb743844a6d44290`: thirteen proof modules covering bounded ROM infrastructure, CTX binding and privacy, finite PQXDH/ratchet games and hybrids, one-step forward secrecy, record integrity, one state-separated composition slice, and an exact restricted one-call result-and-final-heap certificate with public-view probability and advantage equality.
- Target B is the SSProve 0.2.4 framework surface itself: valid typed packages over locations and interfaces, general discrete subdistributions, heterogeneous heap semantics, sequential and parallel composition, identities and interchange, contextual advantage/reduction laws, and pRHL. These facilities are described in the versioned [SSProve guide](https://github.com/SSProve/ssprove/blob/v0.2.4/DOC.md) and the [SSProve paper](https://eprint.iacr.org/2021/397.pdf).
- Target C is the full multi-session, active, primitive-composed, extraction-linked milestone in the repository's computational-security plan rather than either framework's library surface.

The answer is “credible match after a local state-certificate layer” for Target A, “partial, not drop-in” for Target B, and “not yet achieved by either implementation” for Target C.

## Compile-checked native CTX reduction

[`CtxReduction.lean`](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/CtxReduction.lean) defines a game directly over the merged ideal PQXDH record model. An adversary returns one arbitrary raw wire payload and two well-formed explanations containing message material, record associated data, and plaintext. `CtxMisattribution` holds exactly when the real ideal-model `Pqxdh.openRecord` parser and verifier accept both explanations and the explanations differ.

The deterministic theorem `Pqxdh.openRecord_double_opening_yields_ctx_collision` decodes the shared payload, uses its actual parsed Poly1305 tag, and proves that any two distinct successful openings expose unequal CTX preimages with equal `c.blake2b` outputs. The proof uses fixed-width transcript injectivity and the determinism of the same `aeadOpen` call; it assumes neither AEAD integrity nor AEAD key commitment.

`ctxCollisionReduction` runs the same probabilistic adversary and returns those two CTX preimages, using an equal fallback pair only for a payload that fails to parse. The checked capstone

```text
ctxMisattributionAdvantage c A
  ≤ CollisionResistance.crAdvantage c.blake2b (ctxCollisionReduction A)
```

has factor one, no additive loss, and no random-oracle idealization. It is a standard-model reduction conditional on collision resistance of the ideal model's pure BLAKE2b function. VCVio's `CRAdversary` does not encode a PPT cost proof, so polynomial-time preservation is an external inspection obligation; the reducer adds only deterministic parsing and transcript construction.

The checked relabelling specialization uses an honest `sealRecord` as the source payload and proves that acceptance under a distinct target context has the same factor-one reduction. Its pointwise wrong-sequence, wrong-sender, and cross-session corollaries return the exact two CTX transcripts that collide if a record is accepted under any of those changed fields.

The native theorem closure is admission-free. `#print axioms` reports only `propext` and `Quot.sound` for collision extraction and the three pointwise field specializations, and additionally `Classical.choice` for the two probability inequalities; no audited theorem reports `sorryAx`.

A numerical ROM birthday corollary cannot be obtained by rewriting this theorem. `Pqxdh.openRecord` calls a pure `Bytes → Bytes` hash, whereas VCVio's ROM experiment uses monadic oracle queries and a finite output type. Such a corollary requires a separate oracle-parametric record verifier plus a checked correspondence theorem; the generic pilot below does not supply that bridge.

The remaining production bridge is also explicit. The reduction is over the handwritten ideal model, not the Aeneas-extracted implementation. A later refinement theorem must connect the extracted `build_commitment_transcript` representation and adapter hash invocation to `Pqxdh.ctxPreimage` and `Crypto.blake2b` before this result supports a production-code claim.

## Earlier framework pilot

[`VCVioFeasibility.lean`](../../beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/VCVioFeasibility.lean) is imported by the maintained Lean root and contains no `sorry`, `admit`, local `axiom`, or `sorryAx` dependency.

The collision-layer portion instantiates VCVio's generic adaptive lazy-ROM commitment binding theorems with `Aeneas.Std.Array Aeneas.Std.U8 229#usize`, exactly the byte-field type in the Aeneas-extracted `commitment.CommitmentTranscript`, and `BitVec 512`, the production digest width. A checked injection from Aeneas `U8` into `BitVec 8` lets Mathlib's existing fixed-vector instance supply the required finite-type evidence. For any generic binding adversary with query budget `q` and `Unit` salt, `ctx_binding_bound_tight_512` checks VCVio's tight `(q(q - 1) + 2) / (2 · 2^512)` bound, while `ctx_binding_bound_512` also preserves the looser `(q + 2)(q + 1) / (2 · 2^512)` collision-resistance-chain route with the generic verifier's two opening queries made explicit. These remain useful numerical ROM results, but they are separate from the native standard-model CTX theorem because no checked oracle-parametric verifier connects `Pqxdh.openRecord` to `bindingGame`.

The generic pilot treats the 512-bit function as an ideal random oracle; it is not a standard-model BLAKE2b collision-resistance theorem and does not prove transformed-AEAD privacy or ordinary integrity. The new native reduction closes the ideal-model binding-to-collision step without routing through this generic game, while production correspondence, CTX privacy, and ordinary ciphertext integrity remain separate obligations.

The state portion defines a dependent private CKEY oracle with typed `put` and `take` results, an affine `empty/full/taken` store, and a public handler linked sequentially around the private provider. Four exact theorems check successful transfer and tombstoning, a call from an assumed tombstoned state, two sequential calls returning the value at most once, and the public observation after private state is discarded. This demonstrates basic `link`/`runState` behavior, but it does not yet match the accepted SSProve certificate: its hard-coded `Bool` key, one slot, and one `Unit` public operation omit authentication/provenance, role/session checks, paired sibling bodies, the joint sampler, false-provenance early return, the complete two-location observation-and-final-heap normal form, finite-source probability/advantage equality, full lifecycle history, and arbitrary contexts. Discarding state with `run` is definitional here and is not a contextual noninterference theorem.

`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for the four probability-bound theorems and the extracted-constant theorem, and no axioms for the four exact state theorems. In particular, the imported proof path does not report `sorryAx`. The pinned VCVio tree does contain unrelated admitted modules, so this is a result for the pilot's theorem dependency closure, not a complete audit of every upstream module, `unsafe` declaration, or build option.

The accepted SSProve gate has a different reviewed trust policy: Rocq 9.0.0 and SSProve 0.2.4 are pinned, `coqchk` runs, proof-bypass syntax is rejected, and probabilistic modules are allowed exactly `boolp.propositional_extensionality`, `boolp.functional_extensionality_dep`, `boolp.constructive_indefinite_description`, and abstract real numbers `R`. The package-semantics proof deliberately avoids stock `Pr`, `Pr_op`, generic advantage, package-validity, and interchange routes whose dependency closure reaches the rejected infinite-sum interchange principle. Any cross-framework comparison therefore requires a documented no-stronger trust policy, not identical axiom names across Lean and Rocq.

## Historical framework-surface comparison

The following table records why VCVio was selected and which framework features remain available if a future native ideal-model reduction needs them. It is not a parity checklist or a requirement to port an SSProve module.

| Capability | Tracked beaconcrypt SSProve use | VCVio v4.31.0 assessment |
| --- | --- | --- |
| Finite randomized games and event probabilities | All accepted probabilistic capstones use finite sources and direct event probabilities. | Match for this finite layer. `OracleComp`/`ProbComp`, `evalDist`, event probabilities, monotonicity, and finite uniform sampling cover it directly. |
| Adaptive bounded random oracles | `BoundedRom.v` supplies explicit fuel exhaustion as `None`, a hidden finite table, chronological traces, exact count/consistency facts, and witness/extractor reductions. | Likely match after an exact semantic ledger. VCVio has random-oracle implementations, caching, logging, programming, pregenerated answers, and query-bound machinery, but the port must preserve observable exhaustion, trace order, and the exact query-count convention rather than merely rule overflow out. |
| CTX binding | `CtxEventReduction.v` and `CtxGame.v` convert the actual finite double-opening event to a bounded same-run explicit collision witness. | The native pure-hash ideal-model event and factor-one standard-model reduction are now checked. The separate generic ROM pilot still lacks an oracle-parametric `openRecord` bridge, and production/extraction correspondence remains open. |
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

## Historical module-by-module comparison

| SSProve module | Likely VCVio route | Risk |
| --- | --- | --- |
| `ProtocolLabels.v` | Lean finite encodings and injectivity lemmas, reusing extracted constants where representations align. | Low; equality to production arrays still needs a checked bridge. |
| `BoundedRom.v` | Map its fuel, `None` exhaustion, hidden table, chronological trace, exact count/consistency, and witness/extractor rules onto VCVio random-oracle, logging, caching, and query-bound implementations. | Low-to-medium; VCVio has the primitives, but observable exhaustion and trace conventions need checked preservation. |
| `CtxEventReduction.v`, `CtxGame.v` | The native Lean route now defines the actual ideal-model double-opening event and reduces it directly to standard collision resistance rather than embedding it in the generic ROM binding game. An oracle-parametric verifier is still required only for a numerical ROM corollary, and the production/extraction bridge remains open. | Low for the completed standard-model event reduction; medium for either production composition or a separate ROM bridge. |
| `CtxPrivacy.v` | Program the hidden transcript entry and prove identical-until-bad/distribution equivalence outside the logged bad query. | Medium; this is the most important missing pilot theorem. |
| `PqxdhRatchetGames.v` | Direct finite `OracleComp` game definitions and exact challenge-independence/equality proofs. | Low-to-medium. |
| `PqxdhRatchetRom.v`, `PqxdhHybridSecurity.v` | Logged adaptive ROMs and bad-input event reductions over the ordered five-contribution root input. | Medium; exact joint HKDF labels, lengths, and prefix behavior must remain one interface. |
| `RatchetForwardSecrecy.v` | Table programming/coupling at the erased predecessor input with a logged bad event. | Medium. |
| `RecordIntegrity.v`, `RecordIntegrityBound.v` | Logged verification queries, fresh-input partition, and uniform-guess bound. | Medium; the combined authenticator assumption is unchanged. |
| `StateSeparatedComposition.v`, `StateSeparatedPackageSemantics.v` | First reproduce the complete two-slot one-call observation-and-final-heap normal forms and public-view probability/advantage equality, then add a second-call/context-indexed theorem. | Medium-high; this is where lack of a full SSProve package/heap layer creates new local infrastructure. |

## Why parity is not the current goal

Reproducing the tracked SSProve module graph would optimize for framework comparison instead of the security properties exposed by the current ideal Lean models. The native CTX proof demonstrates the preferred unit of work: name a concrete bad event over a maintained model, extract a primitive-breaking witness, lift that implication to an advantage bound, and record the exact implementation-refinement and primitive assumptions that remain.

The same-kernel Aeneas/VCVio arrangement reduces one representation seam because a Lean theorem can mention both handwritten models and extracted types. It does not establish semantic correspondence automatically. For CTX, transcript injectivity and collision extraction are now proved natively for the ideal model; the remaining bridge is an ordinary Lean refinement theorem from extracted transcript construction and adapter use to that model.

The direct CTX reduction imports only VCVio's collision-resistance hardness-assumption module rather than the upstream example binding game. The exact SHA pin remains essential because VCVio's API and active development have moved beyond the 4.31-compatible release, and every production-relevant theorem still needs a transitive admission, `unsafe`, option, and axiom-closure audit.

## Acceptance path

1. Prove the extracted-to-ideal CTX transcript bridge, including byte representation, `LE64`, the exact six-field order, and the adapter's BLAKE2b result representation.
2. Lift the completed wrong-sequence, wrong-sender, and cross-session pointwise corollaries to any narrower protocol-transition games that need separately named advantages.
3. Define the next bad event directly over an ideal PQXDH or ratchet component, prioritizing root-input collisions, message-key/nonce reuse, or a one-step post-erasure disclosure game according to which model/refinement seam is already complete.
4. Use VCVio's oracle and hybrid machinery only where the selected ideal component actually needs adaptive queries or game transitions; do not introduce a random oracle merely to restate a pure-function reduction.
5. Record exact loss, query accounting, classical/PPT scope, primitive assumptions, and extracted-production correspondence for every new capstone, then audit its transitive Lean dependency closure.

Reassess the chosen game or framework if it requires a materially stronger assumption than the protocol claim, if the imported dependency closure cannot be kept admission-free, or if the project requires genuine QROM/QPT claims.

## Commands used

```text
git fetch origin lean
git worktree add /tmp/beaconcrypt-vcvio vcvio
git merge --no-ff -S origin/lean
cd beaconcrypt-core/proofs/lean
lake build BeaconcryptCore.Computational.CtxReduction
```

## Validation

- `lake -K jobs=4 build BeaconcryptCore.Computational.CtxReduction` passed after the field-specific specializations and built the focused 2,672-job target.
- `make -C beaconcrypt-core check-lean` passed and built the complete 3,054-job Lean root; the locked `make -C beaconcrypt-core verify-lean` then passed after fresh Hax/Aeneas extraction and another complete 3,054-job root build, with the monitored generated Lean source files byte-identical.
- `make -C beaconcrypt-core check-inventory` passed after the merged PQXDH modules, proof root, native reduction, documentation, and trust-boundary changes were reviewed and fingerprinted.
- A separate `#print axioms` audit reported `[propext, Quot.sound]` for deterministic collision extraction and the pointwise reductions, `[propext, Classical.choice, Quot.sound]` for the two advantage inequalities, and no `sorryAx` in the native theorem closure. The earlier pilot closure remains as reported above.
- The broader `make -C beaconcrypt-core verify` command reached the known stale F* path and stopped at `split_initial_ratchet_kdf_output` while checking newly regenerated F* from the Lean-enabling source refactor. That expected legacy-path failure is independent of the native Lean reduction; its generated F* artifacts were removed/restored, and the relevant locked Lean verification above passed.

<!-- SPDX-License-Identifier: 0BSD -->

# HB-111: authenticated-root composition

The SSProve proof of concept was retired on 2026-09-23. Its source, build targets, CI job and Rocq/SSProve dependencies are no longer maintained or checked. Historical results below describe the checks performed at those checkpoints; the former files remain available in Git at `a6d126c82364413428d0197190b2482ee9af71d2`. Current computational reductions use Lean/VCVio, and their scope and remaining composition obligations are recorded in [the component roadmap](proverif-vcvio-component-closure.md).

This milestone completes the authenticated-root stage for one actual source-generated target and a bounded adaptive native continuation. It extends the retained HB-109 source scheduler into the same cryptographic experiment as the source authentication, selected-key ML-KEM, secret-input Extract-family and ordinary HMAC reductions. The integration target is `codex/full-proof-composition`. The remaining full-proof work is paused after this stage; this is not a claim that the complete computational interpretation of every ProVerif property is finished.

HB-111 is a new milestone within the HB-82 authenticated-root work. HB-70 remains panic freedom. HB-110 is reserved for the separate evolving-KDF work. The fresh topic is based on `bfe6f18e2673840385a63159bc943bbd19e74706`, retaining the Hax 0.4.0 integration and its thirteenth inventory control. The thirteen HB-109 proof modules are semantically ported from `cdeb159fa0543919697b03956cc2c271a26ed41c`; shared inventory and documentation are reconciled with the newer baseline.

## What the experiment proves

`PqxdhAuthenticatedRootExperiment.actual` executes the original identity, private prekey, KEM and one-time generation in source order, the three source-ordered signatures, the actual optional Phase-1 writer/publication and the adaptive source scheduler. Candidate selection can reject, choose attacker-owned material, return an unchanged honest tuple or change signed fields under the original identity. The theorem does not assume that the selected key is honest.

Only the internally eligible branch receives the root replacement: it accepted the original signed tuple under the generated identity, that identity has not been revealed, and its identity/one-time registration has not been consumed. Accepted changed signed fields under the same unrevealed identity are charged once to the displayed joint weak-EUF reduction. Other accepted candidates, revealed identities, consumed candidates and rejection retain their original common continuation. The full private state, logs, caches, instrumentation, source replies and public transcript remain inside the experiment.

After acceptance, the original Server builder and every allowed adaptive native finish, record, public-source and reveal request run on the reached state. Each matching private root uses the same selected challenge-secret handle, preserving repeated-input correlations. The public postchallenge decapsulation interface blocks the exact challenge ciphertext; private native root processing retains the corresponding original decapsulation behavior. The ordinary CCA reduction owns the challenger-supplied shared secret and uses it only in private routing. The protocol continuation never receives the selected secret key or a direct shared-secret field. Common branches use their original unblocked interfaces.

For the exact constructed reductions, the result is:

`Adv(actual, consistent uniform-root family) <= Adv(joint Ed25519/X25519 weak-EUF) + Pr(ordinary KEM correctness error) + Adv(ML-KEM IND-CCA) + Adv(actual secret-input Extract family) + sum_{j < Q} Adv(ordinary uniform-key HMAC reduction j)`.

Each of the first four terms has coefficient one. There is no identity, session or record guessing factor in this one-generated-target statement. It does not assert coefficient-one selection in a future replicated experiment. The HMAC terms are an explicit ordered sum, not an assumption that every root is independently sampled. One ordinary KEM correctness-error probability covers the entire good-sample coupling, including repeated finishes at the challenge ciphertext; IND-CCA is not used to imply perfect decapsulation correctness.

## Computational and source contracts

| Contract | Exact role and limit |
| --- | --- |
| Correct primitive implementations | The fixed primitive interfaces, including invalid-point rejection, are assumed correct. No primitive algorithm, internal implementation or internal security proof is attempted. |
| Joint identity interface | `PqxdhJointIdentity` retains Ed25519 signatures and X25519 converted-DH use of the same identity seed and has an ordinary fresh-valid forgery winning event. Its permitted related use is an explicit joint contract; ordinary Ed25519 EUF-CMA alone does not automatically simulate it. The stopped forgery reduction never executes the later secret-dependent native continuation. |
| Ordinary one-key KEM interface | Actual generated-key support discharges native optional/ordinary encapsulation compatibility. The selected secret key stays within private interpreters. Functional decapsulation, its ordinary correctness-error experiment and one-key IND-CCA remain separate named interfaces. No cross-public-key injectivity is assumed or obtained. |
| Fixed-zero-salt Extract family | The input is exactly `FF^32 || DH1 || DH2 || DH3 || DH4 || ss`, 192 bytes, with the actual public context and source coordinate distributions, and one shared hidden uniform 32-byte KEM contribution across the family. The full 64-byte Extract output is compared with a consistent family. This distribution-specific security endpoint is an explicit additional assumption; entropy or uniform-secret-key HMAC PRF alone does not imply it. |
| Ordinary Expand endpoint | Each indexed reduction makes at most one ordinary HMAC challenge call under a uniform secret key. The output is the production first-32 projection, repeated inputs retain the same result, and every public HKDF evaluation remains real. No public-HKDF/random-table advantage or former `qRoot / 2^256` production interpretation is used. |
| Source correspondence | The exact initial `RootFields` representation is consumed and derived again at every supported reached prefix. The native accepted branch uses extracted acceptance, the actual pending input and registration identifier, actual root derivation, successful consumption, native builder and complete post scheduler. Existing leaf codec/primitive execution laws remain explicit source contracts; distributional and operational theorems do not prove the entire native adapter or compiler. |
| External runtime boundary | Compiler correctness, allocator/OS behavior, native primitive implementation correctness, physical erasure and foreign-runtime copies retain their existing external scope. Snapshots, persistence, restoration and their consequences are excluded from this proof. |

The actual root client itself supplies the joint Extract distribution. Its transcript is retained in that endpoint rather than replaced by an unspecified independent context. The bound names the advantage of that exact reduction; it does not assert a new universal Extract guarantee for arbitrary public contexts. The later global experiment must establish its own live freshness and reveal conditions before using this component to claim protocol secrecy.

## Reviewed modules

The thirteen retained HB-109 modules and their 63 guarded statements are listed in [the historical scheduler record](phase2-source-scheduler-checkpoint.md). Their source bytes match the retained checkpoint exactly. HB-111 adds the following nineteen modules and 121 guarded statements; each theorem has an actual dependency guard limited to the three standard Lean axioms.

| Module | Guarded statements |
| --- | ---: |
| `PqxdhAuthenticatedRootBoundary` | 4 |
| `PqxdhAuthenticatedRootBudgets` | 14 |
| `PqxdhAuthenticatedRootCommonBounds` | 10 |
| `PqxdhAuthenticatedRootComposition` | 4 |
| `PqxdhAuthenticatedRootCorrectness` | 6 |
| `PqxdhAuthenticatedRootEndpoint` | 7 |
| `PqxdhAuthenticatedRootErrorResources` | 1 |
| `PqxdhAuthenticatedRootEufResources` | 7 |
| `PqxdhAuthenticatedRootExperiment` | 3 |
| `PqxdhAuthenticatedRootGoodSimulation` | 2 |
| `PqxdhAuthenticatedRootPrepareBounds` | 6 |
| `PqxdhAuthenticatedRootSource` | 6 |
| `PqxdhAuthenticatedRootSourceResources` | 13 |
| `PqxdhGeneratedNativeContinuation` | 1 |
| `PqxdhPhase2GeneratedServerFields` | 6 |
| `PqxdhPhase2PostScheduler` | 6 |
| `PqxdhPhase2PostSchedulerBounds` | 12 |
| `PqxdhPhase2SharedBounds` | 12 |
| `PqxdhPhase2SharedKemHandles` | 1 |

The reviewed inventory has 574 entries and 400 handwritten Lean units, retaining all thirteen control entries, including the Hax integration control. All prior paths and categories are preserved; only the maintained Lean root, checker and trust-boundary document change existing fingerprints, alongside the 32 added proof modules.

## Query accounting

All counts below are oracle-call bounds on the named programs under every permitted reply. A uniform count is a call to the uniform oracle, not a complete runtime bound. Deterministic parsing, state management, fixed public HKDF and primitive computations remain actual local work. Explicit generator, writer and auxiliary cost contracts expose their actual programs; there is no opaque budget or security assumption on the entire source preparation or continuation.

Write `L` for the all-query/all-state local callback uniform cap, `A` for the builder auxiliary cap, `W` for the Phase-1 writer cap, and `F` for the postchallenge finish-attempt cap. With the original source scheduler's class budget, define:

`sourceBill(L, budget) = coin + 64*(send + raw + hash) + source + uniform + base + decapsulation + 69*(max(L,64)+1)*finish`.

The preselection driver cost is `D = W + sourceBill(L, preBudget)`. Prefix uniform/base/decapsulation caps are respectively `32 + uPrekey + uOneTime + 2*D`, `bPrekey + bOneTime + D`, and `dPrekey + dOneTime + D`. The same original prefix has signing cap three and identity-creation cap one. Additional preselection signing or creation is explicitly excluded by the caller restrictions; arbitrary postchallenge source creation remains permitted and costed.

Let `T = 64 + 5*A + sourceBill(L, postBudget)`. Common accepted and rejected continuations have ordinary uniform cap `34*T` and base/decapsulation caps `T`, including actual source identity creation. Preparation adds the ephemeral sampler and the maximum of native optional and ordinary failure-branch encapsulation costs in each class. The ordinary outer challenger encapsulation is a separate charge, even when its result is unused by a completed branch.

The postchallenge target continuation has:

| Class | Bound |
| --- | --- |
| Uniform | `64 + 5*A + coin + 64*(send+raw+hash) + 33*source + uniform + 69*max(L,64)*F` |
| Base | `publicBase` |
| Logical decapsulation | `publicDecapsulation + F` |
| Private continued root | `F` |
| Initial plus continued roots | `Q = 1 + F` |

The 69 callback bound includes every attempted finish, including rejected, optional-failure and repeated attempts. Its syntax contains at most one selected logical decapsulation and one private root. The component routing conservatively adds those two caps and therefore allows `publicDecapsulation + 2*F` postchallenge selected decapsulations; this is an upper bound, not a claim that each finish performs two decapsulations.

Let the resulting actual preparation caps be `uPre,bPre,dPre`, target continuation caps be `uPost,bPost,dPost,F`, and evaluated primitive costs be `qKeygen,qEncap,qBase,qDecap`. Define:

`U = qKeygen + (uPre + qBase*bPre + qDecap*dPre + qEncap) + (uPost + qBase*bPost + qDecap*(dPost+F))`.

| Constructed endpoint | Uniform/query allowance |
| --- | --- |
| Ordinary CCA reduction | Prechallenge `(uPre,bPre,dPre)`; postchallenge `(uPost,bPost,dPost+F)` |
| Both fixed CCA worlds | `U+32`, including the branch-independent replacement-secret draw |
| Fair CCA game | `U+33`, including its hidden-bit draw |
| Actual-decapsulation challenger wrapper | `U+32`; this is not the original source sampler |
| Typed source-root wrapper | `U`; the original source has a separate directly proved ledger |
| Extract-family reduction | Uniform `U`, family calls `Q` |
| Real Extract-family game | `32+U` |
| Random Extract-family game | `U+64*Q`, with repeated-input cache reuse |
| Consistent expanded-root game | `U+64*Q` |
| Consistent uniform-root game | `U+32*Q` |
| Each indexed HMAC reduction | Uniform `U+64*Q`, challenge calls at most one |
| Each indexed real/random HMAC game | `64+U+64*Q` |
| Ordinary KEM correctness-error game | `qKeygen+qEncap+qDecap`; one key generation, encapsulation and decapsulation invocation |

`PqxdhAuthenticatedRootSourceResources.actual_uniform` directly bounds the original source sampler by `32 + uPrekey + uKeygen + uOneTime + (2+qBase)*D + uEphemeral + uNative + max((34+qBase)*T, 64+5*A+actualPostBill)`. These generator costs are bounds on their actual evaluated programs, including the original optional native encapsulator. Here `actualPostBill = coin + 64*(send+raw+hash) + 32*source + uniform + qBase*publicBase + 69*max(L,64)*F`. Functional decapsulation contributes no uniform draws while retaining its real deterministic computation and optional failure. The source bill is proved without generator interchange, successful-decapsulation assumptions or distribution-equality cost transport.

`PqxdhAuthenticatedRootEufResources.signing_bound` and `staticDh_bound` give the exact generated joint-EUF reduction signing cap three and converted-static-DH cap `D`. Its `uniform_ledger` gives `U_E = uPrekey + uKeygen + uOneTime + 2*D + qBase*D + qDecap*D` uniform requests in that reduction, and `32+U_E` in the actual joint challenger. These are original evaluated generator and interpreter costs, separate from both the actual source sampler and KEM/KDF challengers. No additional identity reservation or guessing factor is inserted.

## Proof map and remaining scope

The full statement-by-statement explanations are in `doc/formal-verification-analysis.md` under HB-111. The source and experiment modules prove original generation support and branch correspondence; the boundary module connects reached state to native acceptance; correctness and good-simulation modules couple the complete continuation once; the composition module sums the named reductions. `PqxdhAuthenticatedRootBudgets.authenticated_native_root_bound` is the final source-budgeted statement, with the actual reached native Server representation and derived `Q`. Its `cca_reduction_bounds`, `cca_uniform_ledger`, `extract_reduction_bounds`, `extract_uniform_ledger`, `root_and_hmac_uniform_ledger`, `indexed_hmac_bounds` and `error_uniform_bound` instantiate the endpoint rows above. The original sampler row is separately `PqxdhAuthenticatedRootSourceResources.actual_uniform`.

This stage supplies the authenticated-root component needed by the later ProVerif bridge. It does not claim a completed computational interpretation of any replicated symbolic secrecy or authentication event. The remaining work includes evolving 64/76-byte KDF and live-reveal composition, adaptive raw multi-session CTX/AEAD lifting with actual evolving keys, the common symbolic/computational experiment, remaining narrow native adapter obligations, and final event/idealization/selection audits. Those tasks are paused.

Production's sequence-one initial admission is unchanged. The former later-record registration relabel witness is now an omitted-policy diagnostic. The separate permitted X25519 encoding alias still refutes raw complete-response origin; no stronger assigned-ID or raw-transcript equality is asserted here. No Rust, ProVerif theory, wire format, primitive choice or binding interface is changed.

## Changed maintained files

The 32 added Lean modules are the nineteen listed above and the thirteen listed in the HB-109 record. They all live under `beaconcrypt-core/proofs/lean/BeaconcryptCore/Computational/`. The accompanying maintained changes are:

- `beaconcrypt-core/proofs/lean/BeaconcryptCore.lean`
- `beaconcrypt-core/proofs/check-inventory.sh`
- `beaconcrypt-core/proofs/reviewed-inventory.txt`
- `beaconcrypt-core/proofs/trusted-boundary.md`
- `doc/formal-verification.md`
- `doc/formal-verification-analysis.md`
- `doc/composition-assumptions.md`
- `doc/impl/proverif-vcvio-component-closure.md`
- `doc/impl/security-gap-remediation-plan.md`
- `doc/impl/staged-verification-record.md`
- `doc/impl/phase2-source-scheduler-checkpoint.md`
- `doc/impl/authenticated-root-composition.md`

## Completion receipt

The complete locked `make -C beaconcrypt-core verify SHELL="$BASH" PROVERIF_TIMEOUT=900` exited zero using the locked proof environment. It checked all 32 configured ProVerif scenarios, the two auxiliary groups, all 53 general-registration cases with 2,444 exact classifications, all four response-alias subfamilies, 17 transcript-fidelity tests, SSProve policy/assumption/kernel checks for all fourteen configured modules, nine normality-checker tests and the 279 extracted-operation certificates. The final full Lake build passed all 3,455 jobs. The separate five-group `check-proverif-live-material` target and the separate `check-inventory` target also passed. Regenerated proof inputs match the frozen reviewed bytes; no generated artifact changed.

All nineteen new modules passed direct Lean 4.31 checks and their 121 actual dependency guards, in addition to the retained thirteen-module, 63-guard scheduler port. Independent reviewers inspected theorem statements, complete source state, assumptions, correlated-secret routing, candidate branches, query ledgers and the final integration. They approved the code, preserved gates, inventory and plain-English explanations. Only the standard `propext`, `Classical.choice` and `Quot.sound` dependencies occur in the new guarded reports. Repository-wide placeholder/custom-axiom policy, root coverage, inventory and whitespace checks pass. Existing generated-code style and tool deprecation warnings remain unrelated to this change.

The unchanged runtime inputs passed `cargo fmt --all -- --check`, `cargo clippy --workspace --all-targets --all-features --locked`, `cargo test --workspace --all-features --locked` with 297 tests, both no-default-feature role library builds and the 17-test transcript-fidelity target. All 128 runtime/build/binding/schema inputs and the pinned vector revisions remain identical to that validated matrix. No Rust or binding interface changed; cargo mutation testing and Go/Python suites were not repeated, following the requested scope.

The final evidence audit checks 615 exact proof/control/runtime file blobs and both pinned gitlinks. Its frozen manifest SHA-256 is `0dec49ff9639264eff4a5567f0ac66bb7165debf153d856b3e627417523b915b`; the successful aggregate log SHA-256 is `bc52ed99f1cc743789202f59e6acab8a6af0d86a56863f0239e8271e225f6459`. The reviewed inventory itself has 574 entries. A fresh pre-publication fetch still identifies `origin/vcvio` as `8330cdef4f4659931b6764a026cd90c4caf833a4` and `origin/codex/full-proof-composition` as `bfe6f18e2673840385a63159bc943bbd19e74706`.

Publication uses `codex/authenticated-root-completion` with the Codex commit footer, then normal integration into `codex/full-proof-composition`. The publication audit compares the tested blobs to the exact committed tree and verifies equality of local HEAD, fetched remote-tracking ref and direct private-remote object for both topic and composition. A fast-forward retains the same tested commit; any reconciliation changing an input requires new validation. The exact published object is reported with the completed milestone. `vcvio` is unchanged because the broader computational-symbolic proof is still incomplete. Work pauses after this bounded stage.

# BeaconCrypt proof handoff — 2026-10-06

This handoff describes the computational/symbolic verification work as it stood on 2026-10-06. The objective is not complete. The published branch contains substantial source correspondence, bounded ProVerif results, and component reductions, but the common computational experiment and the end-to-end root/record composition are still open.

## Start here

The maintained composition worktree is `/tmp/beaconcrypt-authenticated-root-completion`, on `codex/full-proof-composition`, at `4d4ecf0cf15097c3a53e609ac7d874a6fa8f48a1`. The same commit is recorded as the published `codex/full-proof-composition` and `codex/live-getter-source-profile` head. The most recent publication receipt is in `/tmp/bc-arc-scratch/resume-2026-10-05-codex/native-origin-cut-integration/publication.json` for the preceding integration and the getter receipt is `doc/impl/proof-receipts/live-getter-source-profile.json`.

The central worktree deliberately has pre-existing owner dirt. Preserve it byte-for-byte:

```text
 M rooterberg
 M wycheproof
?? beaconcrypt-core/proofs/lean/statements.out
```

The recorded `statements.out` SHA-256 is `bc35a10599cc89a861b7ac3a186e964d26b2596be99d908d8a8eeecd1de976fa`. Do not reset, clean, or commit those paths as part of proof work. `/home/user/beaconcrypt` is the separate `vcvio` product worktree at `8330cdef4f4659931b6764a026cd90c4caf833a4`; it is not the composition worktree.

Read these before changing anything:

* `AGENTS.md`;
* `doc/impl/handover/pause-2026-10-05/README.md`;
* `doc/formal-verification.md`, `doc/formal-verification-analysis.md`, `doc/composition-assumptions.md`;
* `doc/impl/proverif-vcvio-component-closure.md`, `doc/impl/staged-verification-record.md`;
* `beaconcrypt-core/proofs/trusted-boundary.md`;
* the exact-interface ProVerif guide and the native-origin/KEM-cut guides named below.

The October 5 handoff and this file supersede older plans where they conflict. In particular, the public fixed-HKDF/random-table route is rejected, HB-70 is already panic freedom, snapshots and persistence are outside the theorem, and the approved symbolic tier is bounded tier B. The optional P7 logical in-process compromise extension is not approved.

## Scope and non-negotiable boundaries

Production Rust is authoritative. The primitive implementations are trusted as correct, including invalid-point rejection in Ed25519 and X25519. No implementation proof is wanted for HKDF-SHA-512, ChaCha20-Poly1305, ML-KEM-768, Ed25519, X25519, or BLAKE2b-512. The work must expose ordinary primitive games, exact interfaces, distributions, winning events, reductions, losses, and query bills.

The current approved deployment experiment excludes attacker access to running code and disclosure of the ideal Server's identity keys or secret state. Snapshots, persistence, restoration, physical erasure, allocator/OS behavior, foreign-runtime copies, native primitive implementations, compiler correctness, and codec internals remain external contracts or exclusions. Failed protocol operations, replay, cache consumption, and source state transitions still have to be modeled when they are part of an in-scope protocol execution; excluded persistence must not be smuggled into a freshness theorem.

Never turn symbolic constructor injectivity into a computational theorem without an explicit joint primitive contract. In particular, ML-KEM's symbolic free `mlkem_shared_secret(public_key, coins)` is stronger than generic IND-CCA unless the used interface contract says otherwise. Ed25519/X25519 seed reuse is correlated use and requires the stated joint-use game. A programmable classical random oracle is an explicit contract, not a consequence of collision resistance. Public HKDF evaluations remain real outside the approved restricted zero-salt 192-byte Extract-ROM backend.

## Published composition branch

The central branch currently contains the following relevant published cohorts.

| Ref | Scope | Status and limits |
| --- | --- | --- |
| `34122c10635ce334fe6260ab05cd315ac1aa6a7e` | Exact-interface active strong secrecy ProVerif group | Eight maintained targets: two true paired equivalences, two true exact-response/root-origin auxiliaries, and four confirmed false controls/traces. Two directions are separate; Kr3/Ks2 and the selected private-application profile are explicit. It is bounded symbolic evidence, not a computational bound. |
| `64dcf4ad49a3299ae91b9c487bcddff4f70ef3d9` | Native tuple origin, actual selected-KEM encapsulation cut, and later-record source designation | Thirty existing Lean modules with 122 guarded statements were integrated. The native-origin cohort gives the coefficient-one joint Ed25519/X25519 weak-EUF family and complete all-reply resource bill; the KEM cohort gives the filtered one-key IND-CCA cut and source-order continuation; the later cohort marks the same literal source Builder execution. It explicitly leaves root-input nonexposure, alias/freshness, source-event probability, and global composition open. |
| `4d4ecf0cf15097c3a53e609ac7d874a6fa8f48a1` | Actual source getter/profile boundary | Five direct Rust getters are mapped to current computational fields over twenty Beacon phase cases plus the live Server identity getter. Nine regression tests, fourteen source pins, and focused inventory passed. This is field availability and a reviewed lifetime argument; it is not physical erasure or post-compromise secrecy. |

Earlier published central cohorts remain ancestors: source-billed early record integration (`5ab65a1a`), native registration origin (`6c7aaee2`), selected application secrecy (`19fd13a8`), selected Server-to-Beacon origin (`ac3ec901`), exact-ID record origin (`fa1a174e`), initialized-prefix coupling (`851fd638`), joint identity sampler (`8d2b5cdb`), serial ProVerif CI (`d074f31a`), fail-stop transfer (`7abf30ae`), and pin-origin transfer (`e47f17fc`). Their guides state their exact scopes; none is an end-to-end theorem.

Current maintained counts at the getter checkpoint are 3,198 classified expected ProVerif lines, 185 classified `security` lines, 291 ProVerif models, and 64 validation entries. These are inventory/classification counts, not independent protocol proofs. The older serial free-schedule pass contains 49 exact target results under the approved separate serial-group budget (1,800 seconds per target and 10 GiB per run); it remains bounded symbolic evidence.

## Unmerged work that is safe to inspect

### Raw-accept source cut — root-owned WIP

Worktree `/tmp/beaconcrypt-native-accept-origin-cut`, branch `codex/native-accept-origin-cut`, is based on `64dcf4ad49a3299ae91b9c487bcddff4f70ef3d9`. It is not committed, imported, reviewed, or pushed. It contains exactly four untracked Lean files:

* `PqxdhRegistrationJointAcceptCut.lean` — scans every raw `.accept raw` request, including rejected attempts, and resumes the exact continuation; `scan_finish`, `scan_bound`, and `selected_bound` are checked.
* `PqxdhRegistrationJointAcceptCutSource.lean` — connects that cut to the complete command compiler and preserves owners, native state, private services, primitive caches, and the original optional-answer continuation; `commands_bind`, `commands_resume`, and `pending_command` are checked.
* `PqxdhRegistrationJointCutVerification.lean` — proves the attached verification prefix is the actual public source verification with unchanged consumed state before any challenge interpreter; `verified_pure` is checked.
* `PqxdhRegistrationJointNativeKemOrigin.lean` — proves the selected addressed generated owner has either the actual chronological tuple and native KEM public key, or the already defined native tuple-origin failure; it adds no honest-candidate premise. `selected_source` and `key_or_failure` are checked.

The four latest direct-check records are under `/tmp/bc-arc-scratch/resume-2026-10-05-codex/native-accept-origin-cut/logs/`, all with exit `0`. They were built one file at a time with Lean 4.34, `-j1 -M8000`, and `/tmp/bc-arc-scratch/lean.lock`. These files currently lack the publication machinery: no root import, no `#guard_msgs`/axiom guards, no inventory rows, no prose guide, no independent semantic review, and no commit. A successor should first re-run the four direct checks against the current bytes, clean linter warnings, add guards, and then review before publication.

The next join is to instantiate this source cut inside the initialized report compiler. Keep the raw-accept ordinal distinct from the actual encapsulation ordinal; rejection before encapsulation makes them unequal. The target owner must be selected by a public source handle/index, never by comparing a secret key. Use `verified_pure`, `NativeKemOrigin.key_or_failure`, the existing `PqxdhRegistrationJointFinalCandidate` machinery, and the native-origin coefficient-one transport. Preserve all source/private state and all source query classes.

### Opaque selected-KEM continuation — R1 WIP

Worktree `/tmp/beaconcrypt-registration-joint-service-composition`, branch `codex/registration-joint-service-composition`, has published base `1881878f3cbf21febd1020f04a0d44e2b318c78c` and seven untracked WIP modules:

`PqxdhRegistrationJointKemOpaqueSuffix`, `...OpaqueCore`, `...OpaqueClient`, `...OpaqueReal`, `...OpaqueTail`, `...OpaqueResume`, and `...OpaqueCosts`, plus `doc/impl/registration-opaque-kem-source.md` and an analysis append.

The frozen OpaqueSource22 manifest is `/tmp/bc-arc-scratch/joint-scheduler-resume-2026-10-05/opaque-source22/review-manifest.json`, SHA-256 `09612f506a2cf2873c50721882df0339f628ae7c77806dac03236032327425d4`. It records seven modules, 22 guarded statements, seven empty direct-check logs, allowed axioms `propext`, `Classical.choice`, and `Quot.sound`, and bounds of one private root call, four client internal requests, six tail internal requests, and 64 current native-client uniform calls.

This WIP gives literal post-encapsulation full-state compiler equality, extracted acceptance/cleared-token continuity, source root/erase/consume and pending publication continuity, and a separate functional real fixed-HKDF interpretation. It does not prove an Extract hybrid, context secrecy, a correlated sampler/family property, dynamic repeated-ciphertext finish routing, freshness, target selection, or global losses. Do not expose the candidate/KEM secret through `SecretInputKdf.Context`; the existing context is fully visible to that distinguisher. Repeated uses of one ciphertext with different DH coordinates must remain correlated under one exact joint sampler or be covered by an approved stated contract; do not replace them by independent Extract calls.

### Later-record marked-source WIP

The published branch `codex/evolving-record-composition` is at `94bc9538ebad3f9a74d6c32557a070797a101c8f` and contains the reviewed MarkedTransfer15 comparison. Its independent review is `/tmp/bc-arc-scratch/pv-work/live-reveal-profile/reviews/marked-transfer15.json`, SHA-256 `542111f08fb2bfef115bccf91d1c3498c90503fbbd57a4e4a255d4c0c28a61b4`. It proves same-source compiled/native marker comparison and a coefficient-one same-run nonce-refusal term, but does not bound refusal probability.

That worktree also has five untracked `PqxdhLaterChallengeMarked{Start,Total,Native,Retained,Occurrence}.lean` files. They are WIP only. The remaining join is the same sampled packet/native source execution, then alias exclusion, all reveal/ancestor freshness, inside/used/terminal filters, target/session selection, and a refusal probability term. Do not claim post-compromise recovery or persistence security.

### ProVerif source-scope ledger WIP

Worktree `/tmp/beaconcrypt-proverif-source-scope-ledger`, branch `codex/proverif-source-scope-ledger`, is based on `4d4ecf0cf15097c3a53e609ac7d874a6fa8f48a1`. It has seven documentation/inventory changes and one new `doc/proverif-source-scope.md`; no Lean, production Rust, ProVerif model, query, or primitive contract changes. The frozen manifest is `/tmp/bc-arc-scratch/pv-work/source-scope-ledger/review-manifest.json`, and its source-preservation check covers 1,852 tracked Lean/ProVerif/source paths and all 3,198 verdict lines. Its first attempted Nix inventory invocation was blocked by automatic approval timeout; do not report an inventory pass until a later run exits zero.

The ledger catalogs exact current source profiles and distinguishes 18 selected security-class lines (eight auxiliary origin/identity/root checks) from historical classification. It explicitly retains the false later assigned-ID equality property and does not upgrade bounded symbolic results to computational claims. Obtain an independent semantic review, rerun focused inventory, commit/push with the Codex footer, and only then consider integrating it.

## What has not been proved

The following are the substantive open obligations. They must not be hidden by adding an ambient assumption or by renaming a component theorem.

1. The authenticated root theorem still needs the actual source14 accept/report execution joined to the retained Phase-1 EUF reduction and the selected one-key ML-KEM challenge. The final event must cover honest unchanged candidates, honest changed candidates, attacker-owned candidates, and rejection, without an honest-target premise. The exact 192-byte source root input layout is established, but the candidate/KEM value must stay out of the KDF distinguisher's public context.
2. The Extract/HKDF composition remains open at the actual joint sampler. The old public fixed-HKDF/random-table interpretation is known distinguishable and must not return. Full 32-byte root, 64-byte initial output, 76-byte step output, projections, labels, both directions, evolving keys, skipped keys, replay, permitted reveals, and descendant-only compromise all require one correlated ordered hybrid.
3. The common computational/symbolic experiment is missing. It must model replicated sessions, attacker registrations, raw scheduling, record requests, public transcripts, approved reveals and freshness, compromise timing within scope, replay/consumption, and adaptive final decisions. Every ProVerif ideal operation must map to a precise computational endpoint and its selection/query/loss accounting.
4. The typed CTX/AEAD results have not yet been lifted to the global adaptive raw receive interface. The lift must return challenger-produced optional plaintext, preserve parser rejection, cache/future paths, consumption, replay and failed-operation rollback, count every attempt, and charge target/session/record selection. Snapshots and persistence remain excluded.
5. The evolving-chain source event still needs its sampled/native consumer, alias/freshness assembly, refusal accounting, both directions, skipped/replay state, and common-experiment composition. The reviewed MarkedTransfer15 term is a comparison, not a negligible nonce-refusal theorem.
6. ProVerif coverage remains bounded and profile-specific. The exact current source-scope ledger documents what the maintained groups establish. It does not prove every initial admission sequence 1–51, unbounded schedules, or all later committed states. Any extension must preserve the existing main queries, controls, legacy gates, and mutation matrices and must stay within the separately approved serial budget.
7. The production/source boundary still has remaining acceptance, root, record, rollback/replay, publication, and associated-data joins. The getter audit is only field availability and lifecycle correspondence. Compiler correctness, storage, physical erasure, codec internals, and native primitive internals remain external contracts.
8. The final validation matrix has not been run on a final merged result. Focused changed-module checks, inventory checks, formatting, and prior targeted ProVerif receipts exist, but the final exact-merge `lake build`, forbidden-placeholder/axiom scans, Rust checks, role builds, transcript fidelity, complete configured ProVerif gates, and final make verification remain pending. Mutation testing is required only if production Rust changes.

The later assigned-ID equality theorem is false for current production behavior and must never appear as a claimed result. Initial binding agreement, exact-ID origin, and live-object consumed-set facts do not change that.

## Resume procedure

1. Fetch before every integration and verify the central ref. Preserve the three central dirty paths above. Never edit another worktree's uncommitted files.
2. Create a fresh topic from the fetched composition ref. Port only reviewed WIP files by semantic dependency, not by wholesale merge. Recompute source/artifact hashes and inventory metadata after every port.
3. For Lean, use the existing Lean 4.34 binary and one-module checks first:

   ```text
   flock /tmp/bc-arc-scratch/lean.lock timeout 180 \
     /home/user/.elan/toolchains/leanprover--lean4---v4.34.0/bin/lean \
     -j1 -M8000 --root=<proof-root> -o <scratch>/<module>.olean <module>.lean
   ```

   Use the retained artifact `LEAN_PATH` recorded in the lane's scratch manifest. Work one failure at a time. Do not use `sorry`, `admit`, custom axioms, disabled gates, or circular premises. Every published theorem needs an exact `#print axioms` guard permitting only `propext`, `Classical.choice`, and `Quot.sound`.
4. For ProVerif, use the separate serial group approved by the owner: 1,800 seconds per target and 10 GiB virtual-memory limit. The prior 49-target group consumes nearly all of its three-hour budget; do not append targets to it without a new budget decision. The checker must reject unknown, inconclusive, timeout, or unclassified output.
5. Before each publication, obtain an independent semantic review of theorem statements, source correspondence, assumptions, query accounting, and overclaims. Commit focused changes with:

   ```text
   Co-authored-by: Codex <codex@openai.com>
   ```

   Push immediately, fetch the pushed ref, and verify local HEAD, tracking ref, and direct `git ls-remote` equality. Integrate into `codex/full-proof-composition` only after that review and reconciliation.
6. Do not run the full proof machinery for every local fix. Use single-file Lean checks and focused source/checker tests while developing. Run the full final matrix only after all required joins are integrated. Do not run mutation testing for proof/documentation-only changes.

## Useful evidence paths

* Native-origin integration receipt: `doc/impl/proof-receipts/native-origin-cut-integration.json`.
* Native tuple-origin guide and receipt: `doc/impl/native-tuple-origin-reduction.md` and `doc/impl/proof-receipts/native-tuple-origin37.json`.
* Encapsulation cut guide and evidence: `doc/impl/registration-encapsulation-cut.md` and `doc/impl/proof-receipts/encapsulation-cut72/`.
* Marked-source guide and receipt: `doc/impl/later-challenge-marked-source-comparison.md` and `doc/impl/proof-receipts/later-challenge-marked-source-comparison.json` on the evolving branch.
* Getter guide and receipt: `doc/impl/live-getter-source-profile.md` and `doc/impl/proof-receipts/live-getter-source-profile.json`.
* OpaqueSource22 frozen evidence: `/tmp/bc-arc-scratch/joint-scheduler-resume-2026-10-05/opaque-source22/`.
* Source-scope ledger evidence: `/tmp/bc-arc-scratch/pv-work/source-scope-ledger/`.
* Root progress log: `/tmp/bc-arc-scratch/resume-2026-10-05-codex/NOTES.md`.

This handoff is a resume aid, not a completion claim. The next agent should begin with the four raw-accept cut files and the OpaqueSource22 review boundary, then connect the source event to the KEM/root game without exposing the challenged value through KDF context.

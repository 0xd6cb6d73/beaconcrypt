# BeaconCrypt proof completion handoff — 2026-10-11 (audit rerun and verified 2026-10-17)

This handoff records an independent completion audit of the open obligations listed in [the 2026-10-06 handoff](../pause-2026-10-06/README.md), section "What has not been proved", items 1 to 8. It is written for the owner's final validation. It adds no proof, assumption or contract and no maintained check, and it does not change any theorem, model or production file. The two step 7 programs of the checklist are for the owner's run and are not wired into any gate. It was written by Claude on branch `codex/completion-handoff-2026-10-11`, which is not integrated into the composition branch. Besides this file, the branch adds only a pointer section at the end of `doc/formal-verification-analysis.md` and a pointer paragraph in `doc/impl/handover/README.md`.

## Start here

The audited basis is the composition branch `codex/full-proof-composition` at `2cadb9be1b0575b7fb25b295c9df83ce3c94919d`, equal to its pushed ref when fetched on 2026-10-17. The branch has not moved since 2026-10-11. Its only owner dirt is the untracked `beaconcrypt-core/proofs/lean/statements.out` (SHA-256 `bc35a10599cc89a861b7ac3a186e964d26b2596be99d908d8a8eeecd1de976fa`). The submodules are at `rooterberg` `85c1ae75` and `wycheproof` `b61843a9`.

Each of obligations 1 to 7 was audited on 2026-10-11 (the first obligation 1 run was interrupted and left no result) and again on 2026-10-17. Two cross-cutting audits ran alongside: ASSUME covers every premise of the final theorems, and AXIOMS covers axioms, escape hatches, guards and the inventory. Every audit result was then checked by a separate adversarial verifier that tried to refute it. Where a verifier disagreed with its audit, Claude checked the disputed points against the committed sources before writing this file; the statuses below are the corrected ones. The audits read central only. All Lean probes ran one module at a time against the published `LEAN_PATH` of `2cadb9be`. None of the audits ran `make verify`, a full `lake build`, ProVerif, mutation testing or `nix-collect-garbage`. An independent review of this file on 2026-10-17 found three major and ten smaller defects (among them an incomplete restatement of owner input 13, a Rust test command that skipped `beaconcrypt-core`, and an axiom check with no runnable program); they were fixed in a follow-up commit on this branch, which also adds the step 7 programs.

How owner input 13 enters the statuses. Owner input 13 of the common-experiment plan asks the owner to confirm, per headline, the extension of approved games, idealizations and contracts to the headlines of the common experiment (restated in full under obligation 3 (b)). It has no recorded answer. It therefore conditions every theorem stated in the common experiment: the CE headlines and their LQ-F, D-ct and production forms. It does not condition the component theorems of items 1, 2, 4 and 5, which rest on the decisions and contracts approved for their own lines, nor the premise-free boundary equalities of item 7. Where an obligation of the 2026-10-06 handoff is met only through such a headline composition, that part is reported below as closed in Lean and pending input 13, as for obligation 3.

Summary:

- Obligations 1 and 6 are closed within the approved scope. For obligation 1, owner decision 6 (existential owner address, unread `chosenOwner`) is still recorded as unconfirmed; confirming it cannot weaken a statement.
- Obligations 2, 4 and 5 are closed in Lean. Their component theorems are within the approved scope. The parts that the 2026-10-06 handoff requires and that are delivered only through the common experiment's headlines are pending owner input 13: for obligation 2 both directions, evolving and skipped keys and replay; for obligation 4 the target and session selection; for obligation 5 the common-experiment composition. Obligation 2 also needs the setup-carried `PublicDomain.available` contract listed (see the assumption ledger).
- Obligation 3 is closed in Lean. As a handoff obligation it stays pending until the owner acknowledges three scope points: the initial-response field agreement that was not delivered, owner input 13, and the per-operation accounting.
- Obligation 7 is closed within the approved scope, provided the owner accepts the reviewed transcriptions RT-01 to RT-20 as the last link from the Rust adapter to the Lean source programs. Its production headline forms carry the conditions of the CE headlines and so are pending owner input 13, including `ReadWritable` at the production codec `codec'`.
- No assumption was added to close any obligation, and no component theorem was renamed into a closure.
- One pre-existing ambient contract is carried by every final theorem but is missing from the consolidated CE-13 assumption list: the X25519 public-domain availability laws inside `Setup`. It is called out below and needs explicit owner listing.
- No repository Lean source contains `sorry`, `admit`, a custom axiom or another escape hatch. An exact reachability check finds only `propext`, `Classical.choice` and `Quot.sound`. The maintained guard and policy gates are weaker than that check, so the AXIOMS audit stays partially closed.
- Item 8, the owner's final validation matrix, has not been run. None of the item 1 to 7 modules has ever been compiled together in one `lake build`.

| # | Obligation | Audit status | Verifier | Status used here |
| --- | --- | --- | --- | --- |
| 1 | Authenticated root theorem | closed within the approved scope | agrees | closed within the approved scope; owner decision 6 still unconfirmed |
| 2 | Extract/HKDF composition | closed within the approved scope | agrees, with two qualifiers | closed in Lean; item 2's own theorems are within the approved scope; the CE-composed part (both directions, evolving and skipped keys, replay) is pending owner input 13 (its CE-KT bullet, and for the records also the BLAKE2b and AEAD games); the setup-carried `PublicDomain.available` contract needs listing |
| 3 | Common computational/symbolic experiment | closed within the approved scope, conditional | disagrees | closed in Lean; pending owner acknowledgement of (a) the O21 eleven-field agreement, (b) owner input 13 and (c) the per-operation selection/query/loss accounting |
| 4 | CTX/AEAD lift to the global raw receive | closed within the approved scope | agrees | closed within the approved scope for the lift theorems; the target and session selection, charged only in the CE headlines, is pending owner input 13 |
| 5 | Evolving-chain source event | closed within the approved scope | agrees | closed within the approved scope for the chain lift; the common-experiment composition is closed in Lean and pending owner input 13 |
| 6 | ProVerif coverage | closed within the approved scope | agrees | closed within the approved scope: the obligation's conditions hold; no unbounded coverage is proved |
| 7 | Production/source boundary | closed within the approved scope, conditional | agrees | closed within the approved scope if the owner accepts RT-01..RT-20; the production headline forms are pending owner input 13 like the CE headlines, including `ReadWritable` at the production codec |
| ASSUME | Premises of all final theorems | partially closed | disagrees | closed within the approved scope on the Lean side; documentation defects in the CE-13 list |
| AXIOMS | Axioms, guards, inventory | partially closed | agrees | partially closed: the axiom property holds exactly, but guard coverage and the policy gate have gaps, and there has been no full build |
| 8 | Final validation matrix | not run (owner) | — | open; checklist below |

Owner decisions that remain open are collected in [Owner decisions and acknowledgements needed](#owner-decisions-and-acknowledgements-needed). The owner's checklist is [Item 8: the owner's validation checklist](#item-8-the-owners-validation-checklist).

## Basis, method and what Claude checked

Theorem names below are Lean declarations under `BeaconcryptCore.Computational` unless a namespace is given. Line numbers refer to the files at `2cadb9be`. Every theorem named here, except three, has an exact in-file `#guard_msgs` guard over `#print axioms` listing `propext`, `Classical.choice` and `Quot.sound`. The three exceptions: `PqxdhDeploymentIdealSlots.attach_detach` is guarded as depending on no axioms and `PqxdhDeploymentIdealLaterPool.onBase_view` as depending on `[propext, Quot.sound]` (both are under-reported lists, see the axiom scan), and `Pqxdh.INFO_PQ_ne_INFO_R` (`BeaconcryptCore/Model/Pqxdh/Primitives.lean:93`) has no guard. The exact walk of checklist step 7 covers all three. Every module named here is imported by `beaconcrypt-core/proofs/lean/BeaconcryptCore.lean` and listed in `beaconcrypt-core/proofs/reviewed-inventory.txt` with a matching SHA-256.

The audits' Lean evidence:

- Rebuilds. Single-module rebuilds from central's committed sources against the published `LEAN_PATH`, each through the coordination wrapper with `lean -j1 -M8000` and a 180 s timeout. All exited 0, and the oleans were byte-identical to the published ones. Counts: 28 item 1 modules, 56 item 2 and headline modules, 48 experiment, headline, registration and production modules, the 212-module item 4 closure, 5 item 5 key modules plus the root, and all 25 item 7 modules.
- Semantic comparison. 192 lake-built base modules of the item 5 closure that predate a later commit to their sources were rebuilt and compared semantically (lake-built oleans cannot be compared byte for byte; see the risks). All 192 were identical.
- Kernel replay. Every one of the 1,985 published oleans was kernel-replayed against its published imports. All 1,985 replayed with no failure, and a negative control failed as expected.
- Axiom reachability. An exact axiom-reachability walk was run from all 94,891 project constants. Checklist step 7 gives the program.
- Probes. Mechanical premise and closure probes were run on the headline, production and component theorems. ASSUME's set of 330 final theorems consists of every theorem named in the CE-13 computational column of `doc/proverif-source-scope.md`, in the CE-13 section of `doc/composition-assumptions.md` and in `doc/impl/production-headlines.md` (145 of these names are theorems), all 200 theorems of the six `PqxdhDeploymentProduction*` modules, and the item 2, 4 and 5 components that these theorems consume. Counts "of the 330 final theorems" below refer to this set.

The audits' working files are in the agents' registered scratch area on the shared machine. That area is transient and is not evidence of record, so every finding this handoff relies on is restated here.

Before writing, Claude checked the following against the committed sources:

- Owner input 13 of the common-experiment plan (`doc/impl/common-deployment-experiment-plan.md`, section 16) has no recorded answer. Sections 19 to 27 and the relayed owner decision records of 2026-10-07 to 2026-10-16 do not answer it, and the coordination messages of 2026-10-07 list it as pending.
- The plan section 22 cap loosening is still recorded as awaiting confirmation (also `doc/composition-assumptions.md`, CE-13 "Query bounds").
- The O21 change is a Claude decision (plan section 30).
- The current ideal-operations table (`doc/impl/deployment-experiment.md`, "Ideal operations") has only a "CE endpoint now" column. The plan section 11 table that has selection, query and loss columns is stale.
- The X25519 public-domain contracts:
  - Definitions: `PqxdhServerStaticDhSource.PublicDomain` (`available : ∀ seed input, (joint.staticDh seed input).isSome = accepts input`) and `PqxdhPhase2GapDhSource.PublicDomain` (`available`, `nonzero`).
  - Placement: they are fields `serverDomain` and `beaconDomain` of `PqxdhServerAuthExperiment.Setup` (lines 70-71).
  - Use: the proofs of `PqxdhDeploymentKemTwoSided.kem_transfer_two_sided`, `PqxdhDeploymentIdealCompile.ideal_compile` and `PqxdhDeploymentIdealHandoff.ideal_world_view` use `serverDomain.available`: the reachability walk of checklist step 7, started from each of them, reaches the projection `PqxdhServerStaticDhSource.PublicDomain.available`. Started from item 2's `PqxdhRegistrationJointKemKeyTransfer.allIdeal_loss`, `PqxdhRegistrationJointKemPostSkeleton.opaqueBranch_shared` and `PqxdhRegistrationJointBeaconFinishOnce.slotGame_two`, it does not. The second check of step 7 prints these six results; Claude ran it in that form on 2026-10-17 against the published olean set.
  - Ledgers: they are recorded only in prose, at `beaconcrypt-core/proofs/trusted-boundary.md:449` ("native optional-DH availability law") and `doc/composition-assumptions.md:186` ("public optional availability"). The CE-13 list of `doc/composition-assumptions.md` names only `prefixConsistent` and `setup.wiring` as setup-carried.
  - Origin: they predate the handoff (commits `4136ea17` and `bf5cf596` of 2026-09-24, `Setup` in `aec2ee23` of 2026-09-30). They appear in the Milestone B design's `Setup` (`doc/impl/server-authentication-design.md`, "Every field is an existing functional contract").
- Rust. No production Rust, Go, bindings header, test or example file changed between the handoff basis `4d4ecf0c` and `2cadb9be`. Central's production Rust differs from `vcvio` (`8330cdef`, an ancestor of central, 977 commits behind) only by `5cbd76e3` (HB-95, sequence-one registration check) and `12d5dfcc` (extracted record wrapper): 4 files, +293/−60. Both commits predate the handoff, and neither is in `vcvio` or `main` (`61df2845`). `main` has two documentation-only commits not in central.
- `LEAN_PATH`. The published file exists, and all 42 of its prefixes are present.
- Coordination. No lease or Lean slot was held when this file was written.

## The obligations

### 1. Authenticated root theorem

Status: closed within the approved scope. The verifier agrees. Owner decision 6 is still recorded as unconfirmed (see the remaining gaps); confirming it cannot weaken a statement.

The handoff requires three things. (a) Join the actual source14 accept/report execution to the retained Phase-1 EUF reduction and to the selected one-key ML-KEM challenge. (b) Cover honest unchanged, honest changed and attacker-owned candidates and rejection, with no honest-target premise. (c) Keep the candidate/KEM value out of the KDF distinguisher's public context.

Theorems:

- `PqxdhRegistrationJointAuthenticatedSelectedKem.authenticated_selected_kem` (T5) is the join for (a).
  - Event: `KemRawBridge.Decided ∧ KemRawBridge.GoodKem kemIndex ∧ AcceptOrigin.Protected kemIndex`, on the report coupling `PqxdhRegistrationJointAcceptCutReports.split`.
  - Coupling: its source projection has exactly the distribution of the actual initialized execution of the tagged program, which issues exactly the requests of `work` (`AcceptCutTag.tag_erase`).
  - Bound, every coefficient one: the KEM-ideal raw-ordinal branch, plus one ML-KEM IND-CCA advantage of `KemRawCertified.adversary`, plus the correctness error `KemRawGame.correctnessError`, plus `Σ target < count+1` of the joint weak-EUF advantage of `NativeOriginBound.reduction`.
  - Bills: `authenticated_selected_kem_bills` (T5b).
- `PqxdhRegistrationJointAuthenticatedSelectedKem.classify_final` covers (b). It sorts every coupled execution into one of four cases: no session returned (every rejection), attacker-owned or unprotected, protected with key match at the cut, and the protected address-free final-report failure. `PqxdhRegistrationJointAcceptOrigin.classify` and `protected_bound` support it.
- (c) is covered by two steps:
  - `PqxdhRegistrationJointKemRawOpaque.branchRaw_opaque` (T6) is a premise-free program equality, used in `authenticated_selected_opaque`.
  - `PqxdhRegistrationJointKemKeyTransfer.authenticated_ideal_keys`, `authenticated_all_ideal` and `authenticated_slots` (T8) are each `compose_right` of T5 with item 2's loss. Every Extract game in that loss has `Context := Unit` and sampler `uniform32`, and the HMAC-PRF games sample their own key.
  - Related forms: `PqxdhRegistrationJointKemKeyFirst.authenticated_key_first` and `authenticated_key_last`, and the bills `PqxdhRegistrationJointKemKeyTransfer.idealKeys_bills` and `allIdeal_bills` (T8b), which are declared in module `PqxdhRegistrationJointKemKeyTransferBills` inside namespace `PqxdhRegistrationJointKemKeyTransfer`.
- The supporting components are `PqxdhRegistrationJointKemRawBridge.actual_le_real` (T4) and `PqxdhRegistrationJointKemRawCertified.real_le_ideal`.

Assumptions:

- Explicit premises: `shortRejects` (attached verification rejects inputs shorter than 64 bytes), `FunctionalDecapsulation setup.kem` (a data premise), and the resource premises `certified` and `capacity`. T8 adds `SourceFullCorrect setup.source setup.hmac`.
- Setup-carried laws used by the proofs: `setup.wiring` (`staticDh`, `verifyAttached`, `xPublic`), for T8 also `setup.source.prefixConsistent.ratchetPrefix`, and the `Pqxdh.Crypto` laws `dh_comm`, `xpub_length`, `x25519_length` and `hkdf_length`.
- Not reached: `Pqxdh.Crypto.decap_encap` and every KEM field of `Pqxdh.Crypto`.
- Games: ML-KEM-768 one-key IND-CCA and its correctness error (standard); the HMAC-SHA-512 PRF (standard); the joint Ed25519/X25519 weak-EUF game; Extract on a uniform 32-byte input.
- The joint weak-EUF game and the Extract game are classified as additional assumptions in `doc/formal-verification-analysis.md` (lines 806-807). The audit had called them ordinary, and the verifier corrected that. The owner accepted Extract-uniform32 on 2026-10-06. The joint-use weak-EUF game is the stated joint-use contract that the 2026-10-06 handoff requires for Ed25519/X25519 seed reuse.
- Model: route R1. The "actual" execution already computes the root through the R1 random-oracle table (`PqxdhServerAuthNative.romRootBytes`), so the theorems say nothing about a standard-model HKDF-Extract.

Remaining gaps:

- Owner decision 6 is still recorded as open (`doc/impl/registration-accept-kem-join.md`, `doc/impl/extract-composition-plan.md:387`, plan line 628). It concerns the existential owner address in `Protected` and the unread `chosenOwner`. Confirming it cannot weaken any statement.
- The one-sided statement form of T8 (item 2 plan owner input 5) has only implicit approval.
- The authenticated join (T5/T8) is one-sided by its event shape and fixed to a public target. Two-sided forms exist only for the KEM and key-transfer half (`PqxdhDeploymentKemTwoSided.actual_real_close`, `kem_transfer_two_sided`, `PqxdhDeploymentHeadlineChain.chain_slot_close`, `PqxdhDeploymentHeadlineKeyTransfer.ce_kt_close`).
- The common experiment does not consume T5 or T8. It uses T4, the KEM hop, T6 and item 2's T7 per designated target, and it treats authentication separately (CE-A1, CE-A2, CE-A2pub).
- There is no forward secrecy against a later disclosure of KEM key `kemIndex`.
- Reachability of the bounded event is not shown. The only non-vacuity evidence is the audit's instantiation of every premise on the toy `PqxdhServerAuthJointWitness.setup`, which is not committed.
- No document names T5/T8 as the item 1 closure, and several passages still call item 1 open.

### 2. Extract/HKDF composition at the actual joint sampler

Status: closed in Lean. Item 2's own theorems are closed within the approved scope. The part of the obligation that is delivered only through the common experiment (see qualifier (ii)) is pending owner input 13. The setup-carried `PublicDomain.available` contract needs listing (qualifier (i)). The audit and its verifier had reported "closed within the approved scope, with two qualifiers"; the review of this file showed that qualifier (ii) was too narrow.

Lean builds one correlated ordered hybrid per target `g`. Its steps, in order:

- The real deployment game. Its sampler is the actual joint one: one R1 table shared by every honest root and by the adversary's `hmac` command on the zero-key 192-byte slice, and one ML-KEM challenge secret as the hidden 32-byte suffix of every challenge-derived root.
- CE-9 `PqxdhDeploymentKemTransfer.kem_transfer` (two-sided: `PqxdhDeploymentKemTwoSided.kem_transfer_two_sided`).
- Item 2's G1 and S1b, S1c and S2 hops:
  - G1: `PqxdhExtractRomHiddenSuffix.hidden_suffix_bound`.
  - S1b: `PqxdhRegistrationJointKemPostSkeleton.opaqueBranch_shared`, an equality.
  - S1c: `PqxdhRegistrationJointKemRomSplit.opaqueBranch_split`, `(qAccept+qFinish+qHmac)/2^256`.
  - S2: `PqxdhRegistrationJointKemRootExpand.opaqueBranch_uniform`, the 32-byte root made uniform with HMAC-PRF terms.
- G2: `PqxdhKeyScheduleFromRoot.fromRoot_bound` and `fromRoot_bound_context`, with `PqxdhServerAuthKeySchedule.fromRoot_model` by `rfl`. This step covers the 64-byte initial output, the 76-byte step output and the projections key32/next32/nonce12 and right32, with the labels `INFO_PQ` and `INFO_R` fixed and `Pqxdh.INFO_PQ_ne_INFO_R`. Their layouts match Rust `split_initial_ratchet_kdf_output` and `split_ratchet_kdf_output`.
- T7 and stage T: `PqxdhRegistrationJointKemIdealKeys.opaqueBranch_idealKeys` (T7), then `PqxdhRegistrationJointBeaconFinishOnce.rootClient_two` and `entryClient_two` (stage T, at most two hidden root reads, no premise), `opaqueBranch_allIdeal_two` and `slotGame_two`.
- The item 2 loss: `PqxdhRegistrationJointKemKeyTransfer.allIdeal_loss` and `idealKeys_loss`.
- Item 2's certified premise at the transported caps is discharged as a theorem (`PqxdhDeploymentCompileCaps.compile_full_certified`).
- Equalities to the ideal world: `PqxdhDeploymentIdealCompile.ideal_compile` and `PqxdhDeploymentIdealHandoff.ideal_world_view`.
- The record lift for evolving and skipped keys in both directions: `PqxdhRecordLiftChainLift.chain_lift` over `(sends + 51·receives)·(2·2)` ordered hops, and `PqxdhRecordLift.record_lift`.

The record lift is composed in `PqxdhDeploymentHeadlineChain.records_close` and `records_le` and in the record-consuming headlines, not in `chain_slot`/`chain_close`. The target split is exact, with coefficient one (`PqxdhDeploymentHeadlineChain.split_named`), in `PqxdhDeploymentHeadlineKeyTransfer.ce_kt_sum`, `PqxdhDeploymentHeadlineLor.ce_lor`, the LQ-F forms and the production forms. The LQ-F forms are `PqxdhDeploymentLaterServerItemKeys.later_slots_two`, `PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later_sum` and `PqxdhDeploymentLaterHeadlineLor.ce_lor_later` (whose record lift is `PqxdhRecordLiftLaterLift.later_record_lift`). The production forms are `PqxdhDeploymentProductionHeadlinesClassical.ce_kt_sum`, `ce_lor` and `PqxdhDeploymentProductionHeadlinesLater.ce_lor_later`.

Replay is covered by deterministic zero-loss facts, `PqxdhDeploymentReplay.replay_game` and `PqxdhDeploymentRecordReplay.record_replay_game`. The statement closures of the item 2 and headline theorems reach none of these: the legacy public fixed-HKDF or random-table game, the correlated Extract family's real game or advantage, `productionHiddenRoot`, and `sorryAx`.

Assumptions:

- The R1 restricted Extract random oracle (owner decision of 2026-10-06, extended to item 2).
- The HMAC-SHA-512 PRF.
- Extract on a uniform 32-byte input.
- `SourceFullCorrect`, with `prefixConsistent` and `wiring` carried in `setup`.
- For the headline compositions, in addition: ML-KEM IND-CCA with its correctness error, `FunctionalDecapsulation`, `Phase1ReadBack`, `Phase2ReadBack`, `FrameReadBack` for origin and unknown key share, `KemBound`, `initBound` and `budget.Respects` (`post.Respects` in LQ-F). The record lifts also need the BLAKE2b classical random oracle and the modified-nonce AEAD IND$ and INT-CTXT games.

Qualifiers found by the verifier:

- (i) The CE composition uses the setup-carried `Setup.serverDomain.available` in the proofs of `kem_transfer_two_sided`, `ideal_compile` and `ideal_world_view`, so every headline cited here depends on it. Item 2's own theorems (`allIdeal_loss`, `opaqueBranch_shared`, `slotGame_two`) do not.
- (ii) The hybrid starts from the experiment's real deployment game, and records enter only through the CE composition (`records_close`, `ce_kt_sum` and the record-consuming headlines). So the obligation's full list (both directions, evolving keys, skipped keys, replay) is met only by CE headlines. Owner input 13 asks the owner to confirm, for CE-KT, the R1 Extract-ROM, the HMAC-PRF, Extract on `uniform32`, `SourceFullCorrect`, `prefixConsistent` and ML-KEM IND-CCA with its correctness error and `FunctionalDecapsulation`; for the record headlines it adds the BLAKE2b random oracle and the AEAD games. The 2026-10-06 item 2 decisions settle this only in part (`doc/impl/extract-composition-plan.md`, section 16). They accept the HMAC-PRF and Extract on a uniform 32-byte key as ordinary primitive games without a scope limit, but they extend R1 only "to this line", the item 2 line, and allow `SourceFullCorrect` only "as a premise of T7/T8"; and input 13 still lists all of these for CE-KT. The common-experiment plan reads them as inherited by the experiment (its section 2 table and section 17), but it still lists them under input 13 for confirmation. Until the owner answers input 13, this part of obligation 2 is closed in Lean and pending, as obligation 3 is.

Remaining gaps:

- Permitted reveals and descendant-only compromise hold only vacuously in the classical core, which has no reveal command. They are moot, not discharged. LQ-F covers a post-run reveal of identity seeds and X25519 scalars only, for confidentiality.
- There is no computational root-secrecy statement. The uniform root appears only as an intermediate hybrid world.
- Item 2's own theorems are stated over source14 (registration). Records enter only through the CE composition, by design, which is why qualifier (ii) applies.
- The hybrid is per target, summed exactly. It is not a single all-sessions hybrid.
- Everything holds in the random-oracle model of the slice. No theorem relates the R1 table to production HKDF-Extract.
- Bills count queries and coins, not running time.

### 3. Common computational/symbolic experiment

Status: the Lean content is verified. The verifier's corrected status, which Claude confirmed against the sources, is closed within the approved scope pending the owner's acknowledgement of three points. Until then the obligation is partially closed on those points. The audit had named only (a) and the section 22 caps. The verifier added (b) and (c) and showed that the caps do not block closure.

The experiment:

- The game is `PqxdhDeploymentSecrecy.game`. It runs a generated-seed Server through `PqxdhLiveServerConstruction.construct … none` (identity index 0 in the headlines).
- The adversary is an arbitrary oracle computation over `PqxdhDeploymentInterface.Command`:
  - registration commands: `create` with raw pin bytes and any pin, `bundle`, `accept` on arbitrary bytes, `build` with an adversary payload, and `finish`;
  - the R1 `hmac` and BLAKE2b `hash` random oracles;
  - record commands: `serverSend`, `serverRaw`, `beaconSend` and `beaconRaw`;
  - the secrecy commands `test` and `fresh`.
- Budgets cap every attempt per class (`Budget.Respects`, `IsQueryBoundP` on every path).
- Observation modes O and P; a transcript of every query with its mode-O reply, plus the produced-frame log.
- Adaptive final decisions: an arbitrary event or claim on the observed value, and a guess with a public-view filter for CE-LOR.
- The classical core has no reveal. LQ-F (`PqxdhDeploymentLaterServerGame.game`) adds the approved post-run reveal and claims confidentiality only.

Theorems:

- Headlines (CE-12 part 1):
  - `PqxdhDeploymentHeadlineKeyTransfer.ce_kt`, `ce_kt_close`, `ce_kt_sum`
  - `PqxdhDeploymentHeadlineOrigin.ce_or_b2s`, `ce_or_s2b`
  - `PqxdhDeploymentHeadlineUks.ce_uks_b2s`, `ce_uks_sender`
  - `PqxdhDeploymentHeadlineApp.ce_app`, `ce_app_server`
  - `PqxdhDeploymentHeadlineLor.ce_lor`, `ce_lor_server`
  - Each is an exact sum over `Fin qAccept × Fin qCreate` by `PqxdhDeploymentHeadlineChain.split_named`, with coefficient one.
- Symbolic-eligibility corollaries (part 2):
  - `PqxdhDeploymentHeadlineSymbolic.ce_or_b2s_sym` and siblings
  - `PqxdhDeploymentHeadlineSymbolicLor.symbolic_lor`, `symbolic_lor_bound`
  - `PqxdhDeploymentHeadlineInjective.ce_or_injective_b2s`, `ce_or_injective_s2b`
  - `PqxdhDeploymentHeadlineGap.server_gap_bound`
  - `PqxdhDeploymentHeadlineCollision.identity_collision_game`
- Bills, collisions and agreement (part 2b):
  - `PqxdhDeploymentHeadlineBillsFull.headline_bills`
  - `PqxdhDeploymentHeadlineCtColl.ct_coll_le`
  - `PqxdhDeploymentHeadlineAgree.agreement_statement`, which is a fact about the ideal CTX worlds, not a statement in the experiment. It reaches the experiment only through the part 4 pin and plaintext lifts.
- LQ-F forms (part 3): `PqxdhDeploymentLaterHeadlineKeyTransfer.ce_kt_later`, `PqxdhDeploymentLaterHeadlineApp.ce_app_later`, `PqxdhDeploymentLaterHeadlineLor.ce_lor_later`.
- Billed, closed, pin and plaintext forms (part 4):
  - `PqxdhDeploymentLaterHeadlineGated.later_headline_bills`
  - `PqxdhDeploymentLaterHeadlineClosed.symbolic_lor_later_closed`
  - `PqxdhDeploymentHeadlinePin.ce_pin_b2s`, `ce_or_pin_b2s`
  - `PqxdhDeploymentHeadlinePlain.ce_plain_b2s`, `ce_plain_s2b`
- D-ct closure:
  - `PqxdhDeploymentHeadlineDctWorld.ctgap_term_le` (`ctGapTerm ≤ epsCt`).
  - There are 46 classical and later `_dct` forms. 31 of them are fully closed. The other 15 still carry `ctCollTerm`, and each of those has a fully closed `*_closed*` sibling. Cite the closed forms, for example `PqxdhDeploymentHeadlineDctClosedP2b.symbolic_lor_closed_dct`.
- Registration claims:
  - CE-A1: `PqxdhDeploymentServerAuth.ce_a1`, `PqxdhDeploymentServerAuthBills.ce_a1_billed` and `PqxdhDeploymentServerAuthInjectiveGame.ce_a1_injective`.
  - CE-A2: `PqxdhDeploymentProvenance.a2_bound` and `a2_generated_bound`.
  - CE-A2pub and CE-R1': `PqxdhDeploymentPublishedTuple.a2pub_bound`, `a2pub_owner_bound`, `r1prime_bound` and `r1prime_owner_bound`.
  - CE-R1 and CE-C3: `PqxdhDeploymentReplay.replay_game` and `PqxdhDeploymentRecordReplay.record_replay_game`.
- Production: the 192 theorems of the five production headline modules of obligation 7 (the 189 forms counted there, plus the three helpers `PqxdhDeploymentProductionHeadlinesClassical.ctGapTerm_source` and `ctCollTerm_source` and `PqxdhDeploymentProductionRegistration.support_zero`), obtained through its premise-free whole-game equalities.
- Every loss term is the advantage of a constructed reduction plus explicit statistical terms. The record lifts are proved theorems, not hypotheses.
- A binder scan of 1,597 theorems, 430 of them headline-type, found no premise beyond the documented ones.
- A cross-module axiom walk over 37,817 constants reachable from 16,711 experiment theorems found only the three standard axioms.

Assumptions: those of obligation 2, plus:

- For CE-A1 and the Beacon-side corollaries: twist-inclusive anchored Gap-DH and the joint weak EUF.
- The contracts `X25519ClassLaw`, `X25519ScalarSpread`, `HasAttachedVerificationAdapter`, `ReadWritable` and `shortRejects`.
- The codec contracts of plan section 19.
- The `NoBundleFailure` run condition (option b).
- `ReductionCaps` for the unbilled CE-A1 forms; the billed forms discharge it.

Owner acknowledgement needed:

- (a) The O21 initial-response "eleven-field agreement" endpoint was not delivered as an event in the experiment. CE-A1 (`PqxdhDeploymentServerAuth.A1NoPinnedMatch`) states only a public matching pinned to the Server identity. It states no root, assigned key ID, associated data or payload agreement, so the CE-13 rows A1-delayed, S2b-initial, A1, s2b-A1, b2s-A1, encoding-A1 and the position-1 part of s2b-C1 are partial.
  - This was a Claude decision (plan section 30) and is disclosed. O21 is not among the capabilities the owner accepted as symbolic-only (input 18: O15, O16, O23, O25-O27).
  - The eleven-field agreement itself is proved for the single-Beacon ServerAuth game (`PqxdhServerAuthCommonAuthentication.common_authentication_with_resources`), which CE-A1 consumes.
- (b) Owner input 13 (`doc/impl/common-deployment-experiment-plan.md`, section 16, item 13) has no recorded answer. It asks the owner to "confirm the scope extension to CE of each of the following, per headline":
  - CE-A2, CE-A2pub, CE-R1': joint Ed25519/X25519 weak EUF (`PqxdhJointIdentity`), and `shortRejects` with `setup.wiring`.
  - CE-A1: Gap-DH, the classical programmable R1 Extract-ROM, the classical programmable BLAKE2b random oracle, joint weak EUF, the record and schedule loss terms of `PqxdhRegistrationR1Authentication.generated_authentication` (the plan requires their primitive games to be listed in CE-13), and the premises `X25519ClassLaw`, `X25519ScalarSpread`, `SourceFullCorrect`, `HasAttachedVerificationAdapter`, `ReadWritable`, `Phase2ReadBack` and `FrameReadBack`.
  - CE-KT: ML-KEM IND-CCA with its correctness error and `FunctionalDecapsulation`, the R1 Extract-ROM, the HMAC-PRF, Extract on `uniform32`, `SourceFullCorrect`, and `prefixConsistent` inside `setup`.
  - CE-OR, CE-UKS, CE-APP, CE-LOR: everything above, plus the BLAKE2b random oracle, the modified-nonce AEAD IND$ and INT-CTXT games of the CTX components, and whatever item 4's receive-side lift needs (for example `DecoderAgreement`).
  - CE-R1, CE-C3: nothing (deterministic).
  - The LQ-F, D-ct and production forms are forms of these headlines and carry the same items. The production forms add `ReadWritable` at `codec'`.
  - Each headline family uses its items unconditionally, as explicit premises or reduction advantages. The codec contracts of plan section 19 answer input 14, not input 13.
  - The plan says that these extensions are used only after approval (section 2 table, line 88, and section 17). Its section 17 also says that item 2's R1 extension, Extract on `uniform32` and `SourceFullCorrect` are "inherited exactly as the owner approved them on 2026-10-06". Of those decisions, the R1 extension is scoped to the item 2 line and `SourceFullCorrect` to T7/T8, and input 13 still lists these items for CE-KT and CE-A1 (see obligation 2, qualifier (ii)). The sentence "every item below was approved before (2026-10-06, 2026-10-07)" in the CE-13 section of `doc/composition-assumptions.md` has no owner record behind it for these extensions. They are not hidden: each is an explicit premise or a named advantage.
- (c) The handoff asks for every ProVerif ideal operation's "selection/query/loss accounting". Lean proves selection globally (`split_named`) and query bills globally (`headline_bills`, `later_headline_bills`). The per-operation table is not current: the plan section 11 table still says "Planned" for O5-O9, O18 and O20 and "CE-12" for O21, and the updated guide table gives only the endpoint. The owner can accept the global Lean accounting as meeting the requirement or ask for an updated per-operation table.
- Not blocking: the plan section 22 cap loosening is a choice of bill parameters. The BLAKE2b cap is `qHash + S + R + qTest + qFresh`, and the coin cap is `qCoin + qTest + qFreshBytes`. Every bill is proved at these sound caps. It is still recorded as awaiting confirmation.

Other gaps, all approved partial rows or disclosed exclusions:

- Root secrecy as `attacker(root)` is not computational; CE-RG is not built.
- These are symbolic-only or not claimed: O13 cross-object builds (CE-M is not built), multi-test-session LOR, plaintext-linked unknown key share, `INITIAL_SECRET`, several Server objects, Beacons pinned to other key IDs, and any authentication in LQ-F.
- Some links rest on prose or code inspection: exhaustiveness of the injective forms, key-ID uniqueness, "every published record is a production `Sent`", D2 getter derivability, and the whole symbolic map (by design, input 18).
- No single Lean witness shows that the full premise bundle is jointly satisfiable. `PqxdhServerAuthJointWitness.joint_witness` lacks `HasAttachedVerificationAdapter`, `shortRejects` and `KemBound` in one instance, and nothing covers the production codec.

### 4. Typed CTX/AEAD results lifted to the global adaptive raw receive interface

Status: the lift theorems are closed within the approved scope. The verifier agrees and found citation and counting defects only. The obligation also asks to "charge target/session/record selection". Record selection is charged inside the lift (its hops). Target and session selection are charged only in the CE headlines (`PqxdhDeploymentHeadlineChain.split_named`), so that part is closed in Lean and pending owner input 13, like obligation 3.

Theorems:

- The integrity half is `PqxdhRecordLiftCtxBills.ctxAuthLiftTarget`: an exact sum over `Fin (hops n budget)`, `hops = (S+51R)·(n·2)`, of `integrityLoss`, which contains `2·Σ_{index<qRaw}` INT-CTXT and `qRaw/2^512` with `qRaw = budget.receives`. Its refusal term is 0.
- The privacy half is `PqxdhRecordLiftCtxPrivBills.ctxPrivLiftStatement`.
- `PqxdhRecordLift.ctx_lift` is premise-free. `PqxdhRecordLift.record_lift` and `PqxdhRecordLiftComposition.record_auth_lift` take `SourceFullCorrect`.
- The external challenger answers each hop's opening (`PqxdhRecordLiftCtx.game_real`, `game_replay`).
- Every reachable coordinate is enumerated (`PqxdhRecordLiftCtxAvailability.hybrid_last`).
- The key-free drivers interpret the exact source drivers, including rejection, cached and future paths, rollback and consumption (`PqxdhRecordLiftOpaqueDrivers.receive_interpretation`, `send_interpretation`).
- Origin and binding: `PqxdhRecordFactsOriginClosure.origin_statement` and `PqxdhRecordFactsBindingGlobal.bindingTarget`.
- The link to the experiment's ideal game is `PqxdhDeploymentIdealEnv.c1_idealGame` and `PqxdhDeploymentIdealHandoff.ideal_world_view`. `PqxdhDeploymentIdealFrame.frame_idealD` discharges `Frame`.
- LQ-F: `PqxdhRecordLiftLaterLift.later_record_lift`.
- The lifts are consumed by CE-OR, CE-UKS, CE-APP, CE-LOR and their production and LQ-F forms.
- The lift builds on the existing typed component `AdaptiveCtxPrivacyGuard.canonical_replay_advantage_bound` (through `PqxdhRecordLiftCtxModeBounds.selected_integrity`) instead of renaming it.

Assumptions:

- The BLAKE2b random oracle and the modified-nonce AEAD IND$ and INT-CTXT games, as advantages of explicit reductions.
- `SourceFullCorrect`, the codec laws and the resource premises.
- The functional AEAD fields `aead_open_seal` and `aeadSeal_tag_length`. These are model-level laws: true of a normalized total primitive record, not literally of libsodium on every input.
- The setup-carried contracts of the assumption ledger below.

Remaining gaps:

- Only the designated target's two hidden slots are idealized per hybrid.
- There is no later-mode origin or binding.
- Position 1 of the Server-to-Beacon direction belongs to CE-A1 and is partial (see obligation 3 (a)).
- `PqxdhRecordLiftIdeal.hiddenOpening_malformed` states only the `fromPayload` rejection. The other two rejections hold by definition, as the verifier's probe showed.
- No item 4 module has ever been lake-built.

### 5. Evolving-chain source event

Status: the chain lift is closed within the approved scope. The verifier agrees. The obligation also asks for the "common-experiment composition", which exists only in the CE headlines. That part is closed in Lean and pending owner input 13, like obligation 3.

The obligation is closed through the record-lift route of the common experiment. The family-B line (HB-111/HB-112, MarkedTransfer15 at `94bc9538`) is not used by any statement or premise; `94bc9538` is not on central.

Theorems:

- `PqxdhRecordLiftChainLift.chain_lift` proves `PqxdhRecordLiftIdeal.ChainLiftTarget`. Its aliasing and refusal terms are both `noTerm` (zero, by `rfl`). It is two-sided, holds in every mode and for every budget-respecting adversary, and has the sole contract premise `SourceFullCorrect`. Its target unfolds to `PqxdhRecordLiftIdeal.ChainLiftBool` and `ChainLiftEvent`, which also quantify over environments satisfying `Frame env startup allowance` (discharged later by `PqxdhDeploymentIdealFrame.frame_idealD`), `budget.Respects` and, in the Boolean form, a query bound on the decision. Each of its `(sends + 51·receives)·(n·2)` hops costs one Extract-on-uniform32 and one HMAC-PRF advantage.
- Supporting theorems: `PqxdhRecordLiftChainHybrid.chain_loss`, `chains_terminal`, `terminal_safe`, `PqxdhRecordLiftChainHop.hop_bound` and `PqxdhRecordLiftChainBills.observerAt_total`.
- The kernels are the extracted `ConcreteRatchetKernel.from_counters` (`PqxdhRecordLiftSeed.serverKernel` and `beaconKernel`, by `rfl`). `PqxdhRecordLiftWorldCompiler.run_erasure` ties the compiler to the world.
- The zero CTX refusal rests on `PqxdhRecordLiftProtocolHistory.program_fresh`, consumed by `PqxdhRecordLiftCtxHybrid.allReal_bare`.
- LQ-F: `PqxdhRecordLiftLaterChain.later_chain_lift`, in which the reveal is typed over environment state only.
- Composition: `PqxdhDeploymentIdealHandoff.ideal_world_view`, then `PqxdhDeploymentHeadlineChain.records_le` and `auth_le`, then the headlines.
- The finish-time derivations at sequences 2 to 51 are covered on the experiment side (`PqxdhDeploymentHiddenEntry.finish_accounting`, `PqxdhDeploymentFinishErasure`), inside `ideal_world_view`'s closure.

Assumptions: `SourceFullCorrect`; Extract on uniform32 and the HMAC-PRF, as advantages of explicit observers; the approved reveal profile.

Remaining gaps:

- These are outside the approved profile and are moot, not discharged: freshness, ancestor/descendant compromise, live chain reveals, post-compromise recovery, KCI and forward secrecy against later ML-KEM disclosure.
- Bills count coins and queries, not running time.
- `PqxdhRecordLiftCtxNoRefusal` is imported by `PqxdhRecordLiftCtxHybrid`, but none of its constants is used downstream.

### 6. ProVerif coverage

Status: closed within the approved scope. The verifier agrees.

Item 6 is a scope and preservation condition, not a proof task. Its conditions hold:

- The ProVerif tree (`6deef8cb`), `beaconcrypt-core/Makefile`, `.github`, `beaconcrypt-core/tests`, `beaconcrypt-core/src` and `beaconcrypt/src` are byte-identical at the handoff basis `4d4ecf0c` and at `2cadb9be`. Every main query, control, legacy gate and checker test is therefore preserved.
- The counts are unchanged. There are 3,198 classified lines: 2,841 true, 349 false and 8 unknown. All 185 security lines are TRUE. The six source-projection groups have 16 security lines, and exact-far adds 2.
- The source-scope ledger (`doc/proverif-source-scope.md`) claims no unbounded schedule, no admission at sequences 2 to 51 and no later committed state.
- The CE-13 computational column cites 314 theorems in 58 modules. All of them resolve and are guarded.
- The 20 Python checker regression suites (312 tests) pass on a byte-verified copy.

Evidence per security line, as corrected by the verifier:

| Class | Lines | Evidence |
| --- | --- | --- |
| A | 24 | exact TRUE lines in committed per-target logs |
| B | 58 | exact TRUE lines in the committed `edc701e7` roster log |
| C | 83 | checker summaries only: general registration 61, KEM controller 9, alias 12, registration set 1 |
| D | 20 | the fs group, whose logs exist only on the machine (pass on `974eedf`, 2026-10-05) |

The Rust transcript-fidelity mutation matrices are preserved by byte identity. Their last pass at `2cadb9be` is recorded only in a machine-local receipt.

Remaining gaps:

- By design there is no unbounded or arbitrary-schedule result, no admission at sequences 2 to 51, no result for all later committed states, no global source-to-ProVerif relation and no computational-soundness transfer.
- The 8 UNKNOWN diagnostic lines remain unresolved.
- `trusted-boundary.md:876` and `formal-verification-analysis.md:4190` name only L1, L2 and E19 as open for exact-far. The ledger also lists L3, L4, L5 and the global relation. This is a minor source-scope overclaim in two reference documents, not an overclaim of a verdict.

### 7. Production/source boundary

Status: closed within the approved scope, on condition that the owner accepts the reviewed transcriptions RT-01 to RT-20 as the final link from the unextracted Rust adapter (`beaconcrypt/src`) to the Lean source programs. If the owner instead requires the seven proposed mechanical pins (PB-D1, PB-SURFACE, PB-CHECKS, PB-CAP, PB-TRANSITION, PB-AD, PB-GHOST), obligation 7 stays partially closed until they exist with mutation rows. None exists, by lane decision D-4, not by owner decision. The verifier agrees. The boundary equalities need no answer to owner input 13, but the production headline forms carry the conditions of the CE headlines, so they are pending input 13 as obligation 3 is, including `ReadWritable codec'.frameWrite codec'.frameRead` at the production codec.

Theorems:

- `PqxdhBoundaryDeployment.classical` is premise-free. It equates the source game with `okMap` of `PqxdhDeploymentSecrecy.game` at `codec' = PqxdhBoundaryRecordPrelude.withReader codec reader` and `route' = RawCtxFrameDecoding.sender reader.model`. The equality is on the full returned value, for every setup, codec, reader, checks value, identity index, mode, adversary and runtime.
- `PqxdhBoundaryDeploymentLater.later` is the same for the LQ-F game.
- Both rest on `PqxdhBoundaryDeploymentStep.step_exact`, which covers every command and every state.
- `PqxdhBoundaryDeploymentStep.route_agreement` discharges `DecoderAgreement` at the production instance.
- `PqxdhDeploymentProductionTransfer.chance` and `chance_later` move every probability of the experiment to the source game at identity index 0.
- The production forms: 129 headline forms, 48 D-ct forms (including `PqxdhDeploymentProductionHeadlinesDct.ctgap_term_le`) and 12 registration forms. They are in `PqxdhDeploymentProductionHeadlinesClassical`, `PqxdhDeploymentProductionHeadlinesLater`, `PqxdhDeploymentProductionHeadlines`, `PqxdhDeploymentProductionHeadlinesDct` and `PqxdhDeploymentProductionRegistration`.
- The joins: acceptance in `PqxdhBoundaryRegistrationAccept`, publication in `PqxdhBoundaryPhase1Source` and `PqxdhBoundaryRegistrationBuild`, and records in `PqxdhBoundaryRecordPrelude`, `PqxdhBoundaryRecordExecution` and `PqxdhBoundaryRecordSend`.
- The 25 modules hold 382 guarded theorems: 19 `PqxdhBoundary*` modules and 6 `PqxdhDeploymentProduction*` modules.

Assumptions:

- These premises are carried explicitly at `codec'`:
  - `Phase1ReadBack` and `Phase2ReadBack`;
  - `FrameReadBack`, a joint condition on the abstract writer and the production decoder;
  - `ReadWritable codec'.frameWrite codec'.frameRead`, in 93 forms;
  - `X25519ClassLaw`, `X25519ScalarSpread`, `HasAttachedVerificationAdapter`, `shortRejects`, `FunctionalDecapsulation`, `SourceFullCorrect`, `KemBound`, `initBound` and the budgets.
- The setup-carried contracts of the assumption ledger below.
- External contracts named by the handoff: compiler correctness, storage, physical erasure, codec internals and native primitive internals.
- The D1-D6 deviations and identity index 0.

Remaining gaps:

- The Rust-to-Lean link is reviewed transcription, inside the adapter review units OR-01 to OR-18 of `trusted-boundary.md`. RT-01 to RT-20 are listed only in `doc/impl/production-boundary-ledger.md`.
- Associated data has no dedicated theorem; it is carried by the record equalities and RT-17.
- Root (`PqxdhBoundaryRoot`) and rollback (`PqxdhBoundaryRecordReceiveState`) are leaf modules, so `step_exact` rests on PB-01, 02, 03, 05, 06, 07, 08 and 09.
- The acceptance and birth joins are thin unfoldings of the experiment's existing transcriptions. They are new equalities, not renamed theorems, but they add no evidence about the Rust code.
- Replay and rollback are support facts, not equalities.
- `ReadWritable` is not a plan section 19 codec law. Its use at the production codec falls under owner input 13.
- No claim is made about any deployment that uses only the C, Go or Python bindings, whose Server is persistence-wrapped.

## Assumption ledger

### Hidden-assumption finding

**No assumption was added to close obligations 1 to 7.** Every premise of the final theorems is an explicit binder or a field of an argument structure: there is no `variable` instance, `Fact` or global hypothesis, and no component theorem was renamed. One contract that is a field of the `Setup` argument, and so ambient to every final theorem, is nevertheless missing from the consolidated CE-13 assumption list:

- `Setup.serverDomain.available` (`PqxdhServerStaticDhSource.PublicDomain`): X25519 static-DH availability depends only on a public predicate of the peer encoding, not on the secret seed.
- `Setup.beaconDomain.available` and `Setup.beaconDomain.nonzero` (`PqxdhPhase2GapDhSource.PublicDomain`). The `nonzero` law is redundant at the instance that `Setup` fixes: `beaconDomain` is a `PublicDomain` of `PqxdhJointGapDh.sourceInterface`, whose DH function `PqxdhJointGapDh.sourceScalarDh` returns `none` on an all-zero output, so every `some` value is nonzero by definition. It is still used, by `PqxdhPhase2DhMetadata.selected_nonzero` (`PqxdhPhase2DhMetadata.lean:21`).

Every final theorem quantifies over a `Setup` that carries these fields, and the experiment's KEM-transfer and ideal-world equalities use `serverDomain.available`. The laws are true of clamped X25519 as libsodium implements it: the output is all-zero exactly for small-order peers, independent of the scalar. They predate the handoff and are part of the Milestone B `Setup` design. They are recorded in prose ("native optional-DH availability law", `trusted-boundary.md:449`; "public optional availability", `composition-assumptions.md:186`), but no ledger names them, and the CE-13 list says that `setup` carries only `prefixConsistent` and `wiring`. ASSUME first classified this as a hidden contract. Its verifier reclassified it as an approved but under-documented contract, and Claude agrees after reading the sources. The owner should list it explicitly.

Two further documentation gaps of the same kind:

- The 14 `Pqxdh.Crypto` laws carried by `setup.source.crypto` are listed only generically, as LA-10 of `trusted-boundary.md`. They are model-level laws: true of a normalized total model that agrees with libsodium on every production input, not literally true of libsodium on all inputs.
  - Examples: `verify_sign`, `hkdf_length` beyond 16,320 bytes, and `aead_open_seal` beyond libsodium's maximum message length.
  - `decap_encap` asserts perfect ML-KEM correctness, which real ML-KEM-768 does not have. No final statement reaches it, nor `Pqxdh.Crypto.decap`, `encap` or `kemPub`, so it constrains only unused fields. The protocol KEM is `setup.kem`, whose correctness error is charged explicitly.
- `PqxdhDeploymentServerAuth.ReductionCaps`, a premise of the unbilled CE-A1 forms, is missing from the CE-13 query-bound list. The billed forms `ce_a1_billed` and `ce_a1_injective` discharge it.

### Approved idealizations

- R1: zero-key HMAC-SHA-512 on 192-byte inputs, the zero-salt Extract slice of the root input, is one lazily sampled classical programmable random oracle. It is shared by every honest root derivation and the adversary's `hmac` command (`PqxdhExtractRomFamily.romImpl`). Every other HMAC/HKDF evaluation is real. Approved by the owner on 2026-09-29 for Milestone B and on 2026-10-06 for item 2.
- BLAKE2b-512 as a classical programmable random oracle (`CtxRomAuth.ctxRandomOracle`), shared with the CTX commitments. It comes from the Milestone B and CTX lines; its extension to the experiment's headlines is input 13.
- These are classical models only: there is no QROM claim, and the LQ-F post adversary is classical.

### Primitive games

These enter only as advantages of explicitly constructed reductions, never as hypotheses:

- ML-KEM-768 one-key IND-CCA (VCVio `KEMScheme.IND_CCA_Advantage`) with the explicit correctness error (standard).
- HMAC-SHA-512 PRF (standard).
- Modified-nonce AEAD IND$ and INT-CTXT for ChaCha20-Poly1305 (standard, conventional Boolean IND$; the key-probe IND$ variant is not reached).
- Extract on an independent uniform 32-byte input (additional; accepted by the owner on 2026-10-06).
- Joint Ed25519/X25519 weak EUF (`PqxdhJointIdentity`; additional, non-standard joint-use contract).
- Twist-inclusive anchored Gap-DH (`PqxdhJointGapDh.game`; additional, approved for Milestone B).

These are not reached by any final statement: the correlated Extract family, the legacy fixed-HKDF stream/view/random-table games, `PqxdhHiddenRoot.productionHiddenRoot`, `RawCtxSourceHkdf.rootResponse`, and any collision-resistance game.

### Functional and codec contracts

- Codec contracts approved on 2026-10-06 (plan section 19): `Phase1ReadBack` and `Phase2ReadBack` (premises of 271 and 273 of the 330 final theorems defined under the basis above), `FrameReadBack`, and one codec for registration and records with `DecoderAgreement`. No headline takes `DecoderAgreement`; it is an inner hypothesis of `origin_statement` only, and it is proved at the production instance.
- `ReadWritable codec.frameWrite codec.frameRead`: a restricted writer totality. It is the approved message-model premise of the first-record line (Milestone B and audit remediation C), not a section 19 law. Its use in the experiment and at `codec'` is part of input 13.
- `SourceFullCorrect setup.source setup.hmac`: item 2 decision of 2026-10-06.
- `FunctionalDecapsulation setup.kem`: deterministic decapsulation.
- `X25519ClassLaw`, `X25519ScalarSpread`, `HasAttachedVerificationAdapter` and `shortRejects` with `setup.wiring` (Milestone B functional contracts).
- Setup-carried: `prefixConsistent` and `wiring` (listed), the 14 `Pqxdh.Crypto` laws (LA-10 only), and the `PublicDomain` laws (see the finding above).
- Run condition: `NoBundleFailure` and `NoBundleFailureAt`, bundle-writer option (b), used inside events only.

### Resource premises and statement forms

- Resource premises:
  - `budget.Respects` and `PostBudget.Respects`;
  - `KemBound setup caps`;
  - the runtime initializer bound `initBound` (`qInit`);
  - `certified` and `capacity` (item 1);
  - `ReductionCaps` (unbilled CE-A1);
  - `PqxdhRecordLiftInterface.Frame`, discharged by `frame_idealD`.
- Bills count random coins and oracle calls, not running time.
- Statement-form hypotheses, which are not assumptions:
  - membership of an outcome in the support, and reached outcomes;
  - `ReplayOwnerEvent`;
  - `field ≠ 4`;
  - `mode = .P`;
  - a length-preserving `replace`.

Listed in the ledgers but unused by every final statement:

- the correlated Extract family;
- BLAKE2b collision resistance;
- `NonzeroHonestDh`, `SourceRootCorrect`, `HonestKeyCompatibility`, `RootFields` and `ResponseRefines`;
- `BodyLength`, `RelayLaws` and `ControlLaws`;
- ordinary Ed25519 EUF-CMA;
- `Pqxdh.Crypto.decap_encap`;
- ML-KEM cross-key injectivity (symbolic only).

## Axiom and placeholder scan

Status: partially closed. The verifier agrees.

What is closed:

- An independent comment- and string-stripping scan of all 1,985 Lean files found none of these:
  - `sorry`, `admit`, `sorryAx` or an `axiom` declaration;
  - `native_decide`, `decide +native`, `ofReduceBool` or `ofReduceNat`;
  - `implemented_by`, `extern`, `unsafe` or `opaque`;
  - `partial def`, `csimp` or `#exit`;
  - `run_cmd`, `#eval` or `addDecl`;
  - `import Lean`, or debug and kernel-skip options;
  - a non-local macro, syntax, elaborator or notation (only 1,025 `local notation` declarations).
- An exact axiom-reachability walk imported all 1,985 project modules and followed `getUsedConstants` of every type and value and every constructor, without Lean's precomputed axiom data. It ran from all 94,891 project constants, reached 121,768 constants with 0 unresolved references, and found only `propext`, `Classical.choice` and `Quot.sound`.
- A second implementation reproduced the walk exactly.
- Checklist step 7 gives this walk as a program. Claude ran that program text on 2026-10-17 against the published olean set: it printed the same counts and exited 0 in 20 s. A control file, in which an axiom is reachable only through a structure field type, made it fail with exit 1. The comment- and string-stripping scan of step 7 also reports 0 hits on the 1,985 files; on a control file containing each forbidden token it reports every one.
- The environment declares 33 axiom constants, including Aeneas opaque-type and spec axioms and `native_decide` axioms of Hax `CoreModels`. None is reachable.
- All 19,646 guards are exact and agree with `#print axioms`.
- All 367 distinct deliverable theorems cited for items 2 to 7 carry an exact three-axiom guard, and their exact reachable axiom sets are those three.
- All 2,398 inventory entries hash-match, and the Lean file sets on disk, in git and in the inventory are identical.
- The kernel replay of all 1,985 published oleans passed.

What is not closed:

- Guard coverage in `Computational`. 1,225 public theorems in 72 modules created 2026-08-31 to 2026-09-06, before the rule "guard on every public theorem", have no guard. Nor do 528 private helpers in 194 modules.
- Guard coverage in the older `Model`, `PanicFreedom` and `Refinement` layers, which the AXIOMS audit describes as largely unguarded by design. Public theorems without an in-file guard: 140 of 143 in `Model` (10 modules), 557 of 567 in `PanicFreedom` (12 modules), and 556 of 648 in `Refinement` (63 modules), 2 of which are guarded in another module. That is 1,251 more public theorems with no guard anywhere, and 2,476 in the whole tree.
- The axioms of all these theorems are clean by the walk, but no maintained gate enforces it.
- Guards are not a complete axiom gate in Lean 4.34. `#print axioms` and every `#guard_msgs` guard read per-module axiom lists precomputed when each olean was written (`exportedAxiomsExt`). These lists can under-report axioms that are reachable only through constructor field types. 20 guarded experiment theorems already list fewer standard axioms than they reach, for example `PqxdhDeploymentIdealSlots.attach_detach`, which is guarded as axiom-free. No non-standard axiom is affected today.
- The policy gate. `make check-lean-policy` rejects only `sorry`, `admit`, `axiom` and `sorryAx` in repository sources. It does not reject `native_decide`, `decide +native`, `implemented_by`, `extern`, `unsafe` or `opaque`.
- The dependency layer. The trusted Aeneas and Hax libraries declare axioms, and no ledger records this. `trusted-boundary.md:112` is silent on that layer.
- The full build. The tree has never been checked in one `lake build`.

## What is explicitly not claimed

- Nothing about the persistence-wrapped Server surface of the C, Go and Python bindings, and nothing about persistence, snapshots or restoration.
- No authentication, origin, binding or unknown-key-share claim in the later-quantum mode LQ-F. LQ-F claims confidentiality only (CE-KT-L, CE-APP-L, CE-LOR-L).
- No SSX-origin full-response equality (rows SSX-b2s-origin 3194 and SSX-s2b-origin 3195). Exact full-response equality is false under X25519 encoding aliases; the experiment uses designation by session handle instead. The eleven-field agreement is not restated as an event in the experiment (obligation 3 (a)).
- No tightness. The bounds sum over `qAccept·qCreate` targets and `(S+51R)·4` hops per target, the ciphertext gap has a birthday term, and CE-APP's `2^-min` is charged per target.
- No running-time bound. Bills count coins and oracle calls, so the advantages are small only for efficient reductions, including the arbitrary event, claim, guess and filter functions.
- No computational root secrecy as `attacker(root)`.
- No standard-model HKDF-Extract result: the root step holds in the R1 random-oracle model.
- No QPT or QROM claim.
- No forward secrecy against a later ML-KEM disclosure, no post-compromise recovery and no KCI.
- No claim for a reveal during the run. Freshness and compromise timing are vacuous under the classical profile.
- No computational-soundness transfer of any ProVerif result. No unbounded ProVerif schedule, no admission at sequences 2 to 51 and no claim about all later committed states.
- The later assigned-ID equality is false for production behaviour and is never claimed.
- No claim about Beacons pinned to another Server key ID, about owners with a rejected bundle call in Fresh (for CE-A2pub, CE-R1' and CE-A1), or about accepts under the Server's own identity key.
- Production forms only at Server identity index 0 and one fixed `Checks` value; every security statement uses a generated Server seed (`supplied = none`).
- No proof about Cap'n Proto, libsodium internals, compiler correctness or attacker access to running code.
- These owner-optional extensions are not built: CE-M (several Server objects, cross-object builds), CE-RG (root-guess endpoint), multi-test-session LOR (plan input 7's second question has no recorded owner answer), the `N·Adv(B_guess)` selection form, the screened observation mode R, the PB-* mechanical pins, and a two-sided authenticated root.

## Owner decisions and acknowledgements needed

1. Owner input 13 (plan section 16): confirm, per headline, the extension to the experiment's headlines of the games, idealizations and contracts listed under obligation 3 (b). This includes, for CE-KT, the R1 Extract-ROM, the HMAC-PRF, Extract on `uniform32`, `SourceFullCorrect`, `prefixConsistent` and ML-KEM IND-CCA with its correctness error and `FunctionalDecapsulation`; for CE-A1, the R1 Extract-ROM, Gap-DH, the BLAKE2b random oracle, joint weak EUF, the loss terms of `PqxdhRegistrationR1Authentication.generated_authentication` and its contract premises; for CE-OR, CE-UKS, CE-APP and CE-LOR, in addition the BLAKE2b random oracle and the AEAD games; and `ReadWritable` at the production codec `codec'`. The answer settles the pending parts of obligations 2, 3, 4, 5 and 7. If the owner holds that the 2026-10-06 item 2 decisions already cover the CE-KT items, saying so settles those items.
2. List the setup-carried X25519 `PublicDomain` contracts and the model-level reading of the `Pqxdh.Crypto` laws explicitly in both assumption ledgers. Add `ReductionCaps` to the CE-13 query bounds.
3. Acknowledge that the O21 eleven-field agreement is not an event in the experiment, so the CE-A1 rows are partial.
4. Accept the global Lean selection and query accounting for obligation 3, or ask for an updated per-operation selection/query/loss table.
5. Accept RT-01 to RT-20 as reviewed transcription for obligation 7, or require the seven PB-* pins. The pins would mean Rust test changes and therefore mutation testing.
6. Confirm owner decision 6 (existential owner address in `AcceptOrigin.Protected`, unread `chosenOwner`) and the one-sided form of T8 (item 2 plan input 5). Neither can weaken a statement.
7. Confirm the plan section 22 cap loosening. This is not blocking.
8. Decide whether any owner-optional extension (CE-M, CE-RG, multi-test-session LOR) is wanted.
9. Decide the merge basis. Central contains `5cbd76e3` (HB-95) and `12d5dfcc`, and `vcvio` and `main` do not; the owner handles HB-95.

## Item 8: the owner's validation checklist

Item 8 is the owner's. No agent has run any part of it on a final merged result. The checklist follows `AGENTS.md` and item 8 of the 2026-10-06 handoff. Run it on the exact merge that will be published, in a fresh clone, not in a machine-local worktree or against an olean overlay.

Basis:

- Central `codex/full-proof-composition` at `2cadb9be1b0575b7fb25b295c9df83ce3c94919d`. `vcvio` fast-forwards to it. Merging into `main` is a true merge, and `main` has two documentation-only commits that central lacks.
- This handoff branch adds documentation only and is not part of central; the owner may merge it with central or read it from the branch.
- The published `LEAN_PATH` of `2cadb9be` is `/tmp/bc-coord/leanpaths/2cadb9be1b0575b7fb25b295c9df83ce3c94919d.leanpath`, the value of `coord.sh leanpath current`. It has 42 prefixes and SHA-256 `3c3aa07d8889f6a0ae1bc97a9e92d18cbcc709d5e3032db9a1a6430fd49d0577`.
  - It is a transient machine-local symlink mosaic over 115 build directories under `/tmp`, kept only by the access-time refresh.
  - It reproduces the audits' per-module probes and nothing else. Item 8 must not depend on it.
  - The 88 superseded `LEAN_PATH` files beside it are older trees; use none of them.

Steps:

1. Submodules. Run `git submodule update --init --recursive` and confirm `rooterberg` at `85c1ae75` and `wycheproof` at `b61843a9`.
2. Rust (toolchain 1.96, Cap'n Proto binaries installed). Set `CARGO_TARGET_DIR` to a directory outside the clone for steps 2 to 4, so that a Nix proof-shell copy of the clone (step 5) does not include the cargo build directory.
   - `cargo build --workspace --locked` and `cargo test --workspace --all-features --locked`. The bare `cargo build` and `cargo test` of `AGENTS.md` cover only the default member `beaconcrypt` (`default-members` in the root `Cargo.toml`). They skip the 110 tests of `beaconcrypt-core`, including `beaconcrypt-core/tests/general_registration_admission.rs`. CI runs `cargo test --verbose --workspace` (`.github/workflows/rust.yml`), and the last complete matrix ran `cargo test --workspace --all-features --locked` (285 tests then, `doc/impl/staged-verification-record.md`).
   - The two role/feature checks: `cargo check -p beaconcrypt --no-default-features --features pqxdh,beacon --lib` and `cargo check -p beaconcrypt --no-default-features --features pqxdh,server --lib`.
   - `cargo fmt --all -- --check`.
   - `cargo clippy --workspace --all-targets --all-features --locked`. It fails only on errors, not on lints. The last complete matrix recorded "existing unrelated lint warnings", so `-- -D warnings` would fail on those and is not the gate. Review the warnings instead: a new warning in a file changed by the merge is a finding.
3. Bindings:
   - Go: `cargo build -p beaconcrypt --release --features gobinds`, then `go test -race ./...`.
   - Python: `uv run maturin develop --uv`, then `uv run pytest tests`.
   - Formatting, from the clone root: `uv run black --check --extend-exclude '/(wycheproof|rooterberg|\.lake)/' .` (Black is in the `dev` dependency group; the pinned test-vector submodules are not project sources, and `wycheproof` contains a Python file) and `test -z "$(gofmt -l .)"`. The audits ran neither Black nor `go test`; `gofmt -l .` printed nothing on central's tree on 2026-10-17.
4. Transcript fidelity, inside the proof shell (see "Proof shell" below): `make -C <clone>/beaconcrypt-core check-proverif-transcript-fidelity SHELL=bash`. It runs `test-verdict-classes.py` and `cargo test --locked -p beaconcrypt-core --test proverif_transcript_fidelity`.
5. Full verification: `make -C beaconcrypt-core verify` (add `SHELL=bash` on a host without `/bin/bash`). It enters the locked proof shell and runs these in one invocation, which has never been done since the fs and extension groups were added:
   - `check-toolchain` and `extract-proverif`;
   - `check-proverif`: the legacy roster of 35 scenarios in parallel, plus three groups that are prerequisites of the target and not roster scenarios: live material (5 targets), private application (3 targets) and the KEM-controller authentication gate (1 target);
   - `check-proverif-fs`: the serial free-schedule group;
   - the eleven extension targets;
   - `extract-lean`;
   - `check-lean`: dependency patches, `check-lean-policy`, `check-lean-root`, `check-lean-panic-freedom`, then `lake --rehash build` of all 1,985 modules, which is the exact-merge full build;
   - `check-inventory`.

   Afterwards `git status --short` must show no drift in `beaconcrypt-core/proofs/pro-verif/extraction` or the generated Lean paths. These are the paths `make check-generated` checks, but that target reruns `verify`.
6. Inventory: run `make -C <clone>/beaconcrypt-core check-inventory SHELL=bash` separately inside the proof shell, as `AGENTS.md` asks.
7. Forbidden-placeholder and axiom scans, beyond `check-lean-policy`. Both programs are given in full under "Step 7 programs" below.
   - The source scan. It blanks comments, strings and character literals in every tracked Lean file and reports `sorry`, `admit`, `sorryAx`, `axiom`, `native_decide`, `decide +native`, `ofReduceBool`, `ofReduceNat`, `implemented_by`, `extern`, `unsafe`, `opaque`, `partial def`, `csimp`, `#exit`, `#eval`, `run_cmd`, `run_tac`, `run_elab`, `addDecl`, `import Lean`, `debug.` options, `skipKernelTC`, `trustCompiler`, `allowUnsafe` and every non-local `macro`, `syntax`, `elab` or `notation` command. Expected at `2cadb9be`: `LEAN-SCAN files 1985 hits 0` and exit 0. Any hit exits 1.
   - The exact axiom walk, on the full build's output. It imports every module and follows the constants used by every type, value (opaque values included) and constructor, from every `BeaconcryptCore` constant, without Lean's precomputed axiom data. It fails unless every name resolves and the axioms reached are exactly `propext`, `Classical.choice` and `Quot.sound`. Do not rely on `#print axioms` alone, because of the Lean 4.34 under-report described above. Its second check reproduces the `serverDomain.available` usage finding. Expected output at `2cadb9be`, with exit 0 (the counts change only if the merge changes Lean sources):

     ```text
     AXIOM-WALK roots 94891 reached 121768 unresolved 0
     AXIOM-WALK axioms [Classical.choice, Quot.sound, propext]
     SERVER-DOMAIN PqxdhDeploymentKemTwoSided.kem_transfer_two_sided true
     SERVER-DOMAIN PqxdhDeploymentIdealCompile.ideal_compile true
     SERVER-DOMAIN PqxdhDeploymentIdealHandoff.ideal_world_view true
     SERVER-DOMAIN PqxdhRegistrationJointKemKeyTransfer.allIdeal_loss false
     SERVER-DOMAIN PqxdhRegistrationJointKemPostSkeleton.opaqueBranch_shared false
     SERVER-DOMAIN PqxdhRegistrationJointBeaconFinishOnce.slotGame_two false
     ```

8. Mutation testing. It is required only if production Rust changes. The item 1 to 7 work changed none: `beaconcrypt/src`, `beaconcrypt-core/src`, the Go files, `beaconcrypt/bindings.h`, tests and examples are identical between `4d4ecf0c` and `2cadb9be`. Relative to `vcvio` and `main`, however, central carries `5cbd76e3` and `12d5dfcc`. If the exact merge brings them into a branch that lacks them, that merge is a production Rust change, and the `AGENTS.md` mutation requirement applies to it: run the complete configured `cargo mutants --workspace --jobs 6` and fix every missed or timed-out viable mutant.
9. Nix clean-up. `AGENTS.md` asks for `nix-collect-garbage` after the last Nix-backed verification. On this shared machine it must never run while another agent or process uses Nix; that is the owner's call.

Proof shell. Steps 4, 6 and 7 run inside the locked proof shell. Make a directory `<flake>` that holds only copies of the clone's `flake.nix` and `flake.lock` (the flake refers to no other file), and enter the shell with `nix --extra-experimental-features 'nix-command flakes' develop --no-update-lock-file 'path:<flake>#proofs'`, adding `-c <command>` to run one command. Entering through the clone itself, as the `verify` target does with `path:..#proofs`, copies the whole clone into the Nix store, including any `target/` and, after step 5, the about 22 GiB `.lake` (see the operational notes). `beaconcrypt-core/Makefile` sets `SHELL := /bin/bash`; on a host without `/bin/bash`, such as NixOS, pass `SHELL=bash` to `make`, as the earlier verification records did.

Step 7 programs. Save both files in a directory `<dir>` outside the clone. The programs change no tracked file.

The source scan, `<dir>/lean-scan.py`, runs with `cd <clone>/beaconcrypt-core/proofs/lean && python3 -I <dir>/lean-scan.py` (it does not need the build):

```python
import re, subprocess, sys

# Blank Lean comments (nested /- -/, --), string literals (also s!/m!/f! and r#"..."#) and
# character literals, keeping line structure, then report forbidden tokens.
def strip(t):
    out, i, n, depth = [], 0, len(t), 0
    keep = lambda s: re.sub(r'[^\n]', ' ', s)
    while i < n:
        if t.startswith('/-', i):
            j, depth = i + 2, 1
            while j < n and depth:
                if t.startswith('/-', j): depth, j = depth + 1, j + 2
                elif t.startswith('-/', j): depth, j = depth - 1, j + 2
                else: j += 1
            out.append(keep(t[i:j])); i = j
        elif t.startswith('--', i):
            j = t.find('\n', i); j = n if j < 0 else j
            out.append(keep(t[i:j])); i = j
        elif (m := re.compile(r'r(#*)"').match(t, i)) and (i == 0 or not re.match(r'[\w.\'!?]', t[i - 1])):
            end = t.find('"' + m.group(1), m.end()); j = n if end < 0 else end + 1 + len(m.group(1))
            out.append(keep(t[i:j])); i = j
        elif t[i] == '"':
            j = i + 1
            while j < n and t[j] != '"': j += 2 if t[j] == '\\' else 1
            out.append(keep(t[i:j + 1])); i = j + 1
        elif t[i] == "'" and (i == 0 or not re.match(r'[\w.\'!?₀-ₜ]', t[i - 1])) and \
                (m := re.compile(r"'(\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\'\n])'").match(t, i)):
            out.append(keep(m.group(0))); i = m.end()
        else:
            out.append(t[i]); i += 1
    return ''.join(out)

FORBIDDEN = re.compile(
    r"\b(sorry|admit|sorryAx|axiom|native_decide|ofReduceBool|ofReduceNat|implemented_by|extern"
    r"|unsafe|opaque|csimp|run_cmd|run_tac|run_elab|addDecl|trustCompiler|skipKernelTC|allowUnsafe)\b"
    r"|\bdecide\s*\+\s*native\b|\bpartial\s+def\b|#exit\b|#eval\b|^\s*import\s+Lean\b|\bset_option\s+debug\."
    r"|^(?:@\[[^\]]*\]\s*)?(?:scoped\s+)?(?:macro|macro_rules|syntax|elab|elab_rules|notation|infixl?|infixr"
    r"|prefix|postfix)\b", re.M)

files = sys.argv[1:] or subprocess.run(['git', 'ls-files', '*.lean'], capture_output=True, text=True,
                                      check=True).stdout.split()
hits = 0
for f in files:
    s = strip(open(f, encoding='utf-8').read())
    for m in FORBIDDEN.finditer(s):
        hits += 1
        print(f'{f}:{s.count(chr(10), 0, m.start()) + 1}: {m.group(0).strip()}')
print(f'LEAN-SCAN files {len(files)} hits {hits}')
sys.exit(1 if hits else 0)
```

The axiom walk. Save the following text as `<dir>/axiom-walk-body.lean`:

```lean
open Lean Elab Command

namespace AxiomWalk

/-- Every constant reachable from `roots` through the constants used by types and values
(opaque values included) and by the constructors of inductive types. No precomputed axiom
data is used. Returns the reached constants and the names that do not resolve. -/
def reach (env : Environment) (roots : Array Name) : NameHashSet × Array Name := Id.run do
  let mut seen : NameHashSet := {}
  for r in roots do seen := seen.insert r
  let mut work := roots
  let mut missing : Array Name := #[]
  while 0 < work.size do
    let c := work.back!
    work := work.pop
    match env.find? c with
    | none => missing := missing.push c
    | some ci =>
      let mut used := ci.type.getUsedConstants
      if let some v := ci.value? (allowOpaque := true) then used := used ++ v.getUsedConstants
      if let .inductInfo iv := ci then used := used ++ iv.ctors.toArray
      for d in used do
        unless seen.contains d do
          seen := seen.insert d
          work := work.push d
  return (seen, missing)

end AxiomWalk

open AxiomWalk in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let roots := env.constants.map₁.fold (init := #[]) fun acc n _ =>
    match env.getModuleIdxFor? n with
    | some i => if (`BeaconcryptCore).isPrefixOf mods[i.toNat]! then acc.push n else acc
    | none => acc
  let (seen, missing) := reach env roots
  let found := seen.fold (init := #[]) fun acc n =>
    if (env.find? n) matches some (.axiomInfo _) then acc.push n.toString else acc
  logInfo m!"AXIOM-WALK roots {roots.size} reached {seen.size} unresolved {missing.size}"
  logInfo m!"AXIOM-WALK axioms {found.qsort (· < ·)}"
  unless missing.isEmpty && found.all (["Classical.choice", "Quot.sound", "propext"].contains ·) do
    throwError "AXIOM-WALK FAILED"

open AxiomWalk in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let c := `BeaconcryptCore.Computational
  let target := c ++ `PqxdhServerStaticDhSource.PublicDomain.available
  for t in [`PqxdhDeploymentKemTwoSided.kem_transfer_two_sided,
      `PqxdhDeploymentIdealCompile.ideal_compile, `PqxdhDeploymentIdealHandoff.ideal_world_view,
      `PqxdhRegistrationJointKemKeyTransfer.allIdeal_loss,
      `PqxdhRegistrationJointKemPostSkeleton.opaqueBranch_shared,
      `PqxdhRegistrationJointBeaconFinishOnce.slotGame_two] do
    unless env.contains (c ++ t) do throwError "missing {t}"
    let (seen, _) := reach env #[c ++ t]
    logInfo m!"SERVER-DOMAIN {t} {seen.contains target}"
```

After step 5, inside the proof shell, build the walk file from the import list of every tracked module and run it with the full build's oleans:

```sh
cd <clone>/beaconcrypt-core/proofs/lean
{ git ls-files 'BeaconcryptCore.lean' 'BeaconcryptCore/*.lean' | sed 's/\.lean$//; s|/|.|g; s/^/import /'
  cat <dir>/axiom-walk-body.lean; } > <dir>/AxiomWalk.lean
lake env lean <dir>/AxiomWalk.lean
```

Expected resources. Sources: committed files where they exist; otherwise measurements on this machine recorded by the coordination tooling and the audits, which are restated here because those records are machine-local.

| Step | Time | Memory | Source |
| --- | --- | --- | --- |
| Full `lake --rehash build` | Unmeasured. The last full build (`edc701e7`, 2026-10-01) had 4,728 lake jobs for 1,186 handwritten Lean files; there are now 1,978 handwritten and 7 generated, so expect proportionally more. Single-module compiles take 3 to 7 s; sequential rebuild samples ran 5 to 6.5 s per module including queueing (192 modules in 1,219 s), so about 3 h on one worker for the 1,985 project modules, less in parallel. Dependency builds (Mathlib v4.34.0, VCVio, Aeneas and Hax with the repository patches) come on top unless their outputs are reused. | Unmeasured for a full build. A single Lean check peaks at 3.97 GiB RSS on average and 4.32 GiB at most, mostly shared olean page cache. The coordination class for an 8-worker `lake build` is an 8,192 MiB estimate. Heartbeat limits of one full build are unmeasured. | `doc/impl/handover/pause-2026-10-01/integrated-evidence/beaconcrypt-common-integration-after-make.json` (job count); machine measurements (RSS, rebuild timings) |
| `.lake` disk | about 22 GiB per full tree; 249.7 GiB free on 2026-10-17 | — | machine survey of 2026-10-07; disk report of 2026-10-17 |
| fs group (`check-proverif-fs`) | 2 h 54 min wall in the last pass, 96.5% of the about 3 h OD7 budget; CI allows 210 min; must run serially and alone on the machine | fs-registration A1 kept only 3.3% of the 10 GiB address-space cap as headroom (peak 10,135,500 KiB, 9.67 GiB) | `doc/impl/proverif-free-schedule-records-b2s.md` (wall time in "Budget (OD7)", A1 peak at line 179); `.github/workflows/formal-verification.yml` |
| Extension group | CI allows 180 min; 1,800 s and 10 GiB per target; SS-b2s took 1,426 s of its 1,800 s cap | up to 10 GiB per target | `.github/workflows/formal-verification.yml`; OD7; `doc/impl/handover/resume-2026-10-05/active-strong-secrecy/proverif-receipts.json` |
| Legacy roster (`check-proverif`) | the general-registration family has a 240 min CI job | 35 scenarios at once (`-j35`); the median recorded ProVerif run on this machine peaks at 0.65 GiB, but the roster's combined peak with 35 parallel scenarios is unmeasured | `.github/workflows/formal-verification.yml`; `beaconcrypt-core/Makefile`; machine measurement |
| `check-inventory` | about 2 min per run in the proof shell | unmeasured (2,048 MiB lease estimate) | machine lease history |
| Transcript fidelity | 12 to 15 s per test run; about 20 to 30 s per warm cargo invocation | unmeasured (3,072 MiB lease estimate at `CARGO_BUILD_JOBS=2`) | guides (for example `doc/impl/kem-functional-graph.md`); machine lease history |
| Mutation suite, if required | 1,173 cases in 36 min with `--jobs 6` (last complete run) | — | `doc/impl/staged-verification-record.md` |
| Step 7 programs | source scan about 15 s; axiom walk 20 s against the published olean set | axiom walk 5.0 GiB peak RSS | Claude's runs of the step 7 program text on 2026-10-17 (machine-local) |

Operational notes for the owner's run:

- Proof-shell copy. `beaconcrypt-core/Makefile` uses `PROOF_SHELL := path:..#proofs`, so every `nix develop` copies the working tree, including a built `.lake` of about 22 GiB, into the Nix store. Run `make verify` once in the fresh clone. For any rerun, enter the proof shell from a separate directory that holds only `flake.nix` and `flake.lock` (`nix develop --no-update-lock-file path:<that directory>#proofs`), then run `make -C <clone>/beaconcrypt-core verify-in-shell` (with `SHELL=bash` where needed; see "Proof shell" above).
- ProVerif lock. Ten extension checkers take a blocking `flock` on their default lock `/tmp/bc-arc-scratch/proverif.lock`, and the Makefile passes no `--lock`. Do not run the gates under `coord.sh pv`, which holds that lock for the whole command and would deadlock (a visible hang, not a false pass). Make sure no agent holds the lock during the run. The checkers create `/tmp/bc-arc-scratch` if it is absent.
- Machine load. Pause both agents' heavy jobs; the fs group needs the machine to itself.

## Known risks

- **Modules never built together.** No full `lake build` has ever covered the item 1 to 7 modules. None of the modules of the `PqxdhRegistrationJoint*`, `PqxdhDeployment*`, `PqxdhRecordLift*`, `PqxdhBoundary*`, `PqxdhExtractRomHiddenSuffix` and `PqxdhKeyScheduleFromRoot` families (491 modules) has an olean in central's `.lake/build`. That directory was last written on 2026-10-01 and holds 1,057 module oleans: 1,056 `BeaconcryptCore.*` modules and the root. The published `LEAN_PATH` resolves 908 modules to it; for the other 149 it resolves to oleans in other directories.
  - The evidence is per-module `lean -o` builds stitched together through the published `LEAN_PATH` from 115 build directories.
  - 563 lake-built modules have an olean older than some transitive import, so lake would rebuild them. Kernel replay of all 1,985 published oleans passed, and the 95 modules whose direct import was regenerated after them re-elaborate cleanly.
  - Lake-built oleans cannot be compared byte for byte with `lean -o` rebuilds: they embed the package and sometimes the source path. They were compared semantically instead.
  - Only item 8's build settles consistency.
- **Stale `LEAN_PATH` files not retired.** 88 superseded `LEAN_PATH` files are still pinned beside the current one. They could not be retired because the protocol retires a superseded file only after the other agent acknowledges the newer integration, and Codex never did: Codex has been inactive since 2026-10-09 23:39, and 54 Claude requests and integration announcements await acknowledgement. They keep old overlay directories alive and must not be used. The mirrors also link `.olean` and `.ilean` independently, so editor positions can mislead, for example for `PqxdhRegistrationScheduleSurface`.
- **HB-95 and the merge basis.** `origin/main` (`61df2845`) and `vcvio` (`8330cdef`) lack `5cbd76e3` (HB-95, the sequence-one Beacon registration check, `beacon.rs:467-469`) and `12d5dfcc`. Every PB anchor, RT review and Rust spot check was made against central's Rust. A final merge onto a base without them would invalidate the PB-06 and PB-11 anchors. The owner handles HB-95.
- **/tmp volatility.**
  - The systemd-tmpfiles cleaner deleted 18 tracked central files and 2,041 submodule files; they were restored on 2026-10-16.
  - It also deleted 522 tracked files of the shared dependency worktree `/tmp/beaconcrypt-server-auth-ctx-observer-integration`, including `beaconcrypt-core/proofs/lean/lakefile.toml`, `lean-toolchain` and `patches/`, and 575 of `/tmp/beaconcrypt-server-auth-common-integration`. Their `.lake` outputs, which supply dependency oleans of the published `LEAN_PATH`, are intact. This is not yet recorded in a coordination decision.
  - Committed documents contain about 16,400 `/tmp` references in 377 files. The 21 production receipts hold about 1,540 of them, and their evidence will not survive the cleaner. Restoring the dependency worktrees from their git objects, and extending the access-time refresh to them, are owner decisions.
- **Axiom gate.** In Lean 4.34, guards can under-report (see above), and `check-lean-policy` does not reject `native_decide`, `implemented_by`, `extern`, `unsafe` or `opaque`. A future change that reaches a dependency axiom through a structure field could pass every guard and the gate. The step 7 programs check both properties for the owner's run, but they are not maintained gates; committing them as reviewed checks would be a separate, owner-approved change.
- **ProVerif margins.** The fs group uses 96.5% of its time budget, and A1 uses 96.7% of the memory cap. The general-registration checker changed after its last solver run; its expected verdicts are AST-identical. The complete configured gate has never run in one invocation.
- **Stale Lean docstrings.** Fixing the stale docstrings listed below changes oleans. Any such edit before item 8 needs those modules and their dependents re-checked, and the inventory re-hashed.
- **No joint-satisfiability witness for the full premise bundle in Lean.** The production codec's satisfiability is a prose argument (`doc/impl/production-headlines.md:80`).

## Documentation defects found by the audits (not fixed here)

Most of these understate what Lean proves. The exceptions, which say slightly more than the sources support, are the two exact-far lines (obligation 6), the incomplete CE-13 assumption list with its approval sentence, the quoted under-reported axiom lists and the HB-111 wording. None claims a Lean statement that does not exist. Line numbers are at `2cadb9be`. One further defect is fixed on this branch: `doc/impl/handover/README.md` named the 2026-10-01 pause handoff as current, and now has a pointer paragraph to the later handoffs, with the old paragraph kept as history.

- Assumption lists:
  - `doc/composition-assumptions.md`, CE-13 section: the setup bullet omits the `PublicDomain` laws and the `Pqxdh.Crypto` laws, the query bounds omit `ReductionCaps`, and the cap loosening is still marked as awaiting confirmation.
  - `trusted-boundary.md:918`: the parenthetical enumeration is incomplete.
  - The T8 paragraphs (`trusted-boundary.md:910`, `composition-assumptions.md:226`) omit `prefixConsistent.ratchetPrefix`.
- `beaconcrypt-core/proofs/trusted-boundary.md`:
  - Lines 843, 847 and 856 still call the item 7 joins pending, and there is no entry for 14 of the 25 item 7 modules.
  - RT-01 to RT-20 are not listed.
  - Lines 896 and 904 still call item 1's context clause open.
  - Lines 876 and 112: see obligation 6 and the axiom scan.
- `doc/formal-verification.md`:
  - It never mentions the experiment's headlines, the R1 item 2 route or the record lifts.
  - Lines 48, 58 and 134 call the composition open; line 55 says the common computational interpretation remains open, which is arguably still accurate under owner input 18.
  - Line 5, and `composition-assumptions.md:13`, say HB-111 "closes the authenticated-root composition". HB-111 is not the item 1 theorem.
- `doc/formal-verification-analysis.md`:
  - Line 4752 calls item 1 open.
  - The S4 record-lift section (from line 5112) does not name `PqxdhRecordLiftProtocolHistory.program_fresh` and `PqxdhRecordLiftCtxHybrid.allReal_bare` as the source of the zero CTX refusal.
  - Lines 5206 and 5216 call origin and binding open.
  - Line 4190: see obligation 6.
- `doc/impl/common-deployment-experiment-plan.md`: the section 11 table and section 13 are stale.
- `doc/impl/deployment-experiment.md`: the ideal-operations table has no selection or query columns.
- `doc/proverif-source-scope.md`: lines 64-70 predate CE-13.
- `doc/impl/common-deployment-experiment.md`: lines 2119, 2182 and 2212 quote the under-reported axiom list of `PqxdhDeploymentIdealLaterPool.onBase_view`.
- `doc/impl/extract-composition.md`: its status line is stale.
- `doc/impl/proof-receipts/extract-composition-inc4.json`: records a pre-review hash of `PqxdhRegistrationJointKemKeyFirst.lean` (a docstring-only fix, `7f795e19`).
- Module docstrings:
  - `PqxdhRecordLiftComposition`, `PqxdhRecordLiftCtxBills`, `PqxdhRecordLiftInterface` (including `Caps.derivations`), `PqxdhRecordLiftLater`, `PqxdhRecordLiftCtxHybrid` and `PqxdhRecordLiftWorld`: they still describe delivered parts as open.
  - `PqxdhRegistrationJointKemIdealKeys` and `PqxdhRegistrationJointKemSecondEntry`: they still say stage T is not built.

## Coordination state when this file was written (2026-10-17)

- Agent jobs: no lease, Lean slot, ProVerif lock or integration lease was held, and disk was at level OK (249.7 GiB free).
- Codex: inactive since 2026-10-09. Claude owns the item 2, 3, 4, 5 and 7 lanes and CE-14 (owner decisions of 2026-10-08 and 2026-10-10).
- This branch, `codex/completion-handoff-2026-10-11` (worktree `/tmp/beaconcrypt-completion-handoff`), is registered to Claude, is documentation only and is not integrated into central.

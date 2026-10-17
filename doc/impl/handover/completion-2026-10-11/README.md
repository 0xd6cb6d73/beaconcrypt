# BeaconCrypt proof completion handoff — 2026-10-11 (audit rerun and verified 2026-10-17; updated after the owner decisions of 2026-10-17)

This handoff records an independent completion audit of the open obligations listed in [the 2026-10-06 handoff](../pause-2026-10-06/README.md), section "What has not been proved", items 1 to 8. It is written for the owner's final validation. It adds no proof, assumption or contract and no maintained check, and it does not change any theorem, model or production file. The two step 7 programs of the checklist are for the owner's run and are not wired into any gate. It was written by Claude on branch `codex/completion-handoff-2026-10-11`, together with a pointer section at the end of `doc/formal-verification-analysis.md` and a pointer paragraph in `doc/impl/handover/README.md`; that branch was integrated into the composition branch at `d95dd6dd` on 2026-10-17.

Update of 2026-10-17. After the integration, three things changed, and this file was updated in place on branch `codex/completion-fixes-2026-10-17` (documents only; not yet reviewed or integrated). (1) The owner decided on 2026-10-17: plan section 16 input 13 is approved as listed, and the two shared dependency worktrees damaged by the `/tmp` cleaner are restored and protected; Claude accepted the plan section 22 cap loosening under the owner's delegation (plan section 131). (2) O21 was built, reviewed and integrated: central is now at `c6ee2307`, which adds four Lean modules stating ten of the eleven session fields of point (a) of obligation 3 as an event of the experiment. (3) The documentation defects found by the audits and by the confirming review of this file at `d95dd6dd` were fixed, the per-operation selection, query and loss table of obligation 3 (c) was written, and the step 7 source scan was widened. The statuses below are those after these changes; where the text describes the state at `2cadb9be`, it says so. The section "Documentation defects found by the audits and their resolution" lists what was fixed and what was not.

## Start here

The audited basis is the composition branch `codex/full-proof-composition` at `2cadb9be1b0575b7fb25b295c9df83ce3c94919d`, equal to its pushed ref when fetched on 2026-10-17. The branch had not moved since 2026-10-11; later on 2026-10-17 it moved to `d95dd6dd` (this handoff) and `c6ee2307` (O21), see the update paragraph above. Its only owner dirt is the untracked `beaconcrypt-core/proofs/lean/statements.out` (SHA-256 `bc35a10599cc89a861b7ac3a186e964d26b2596be99d908d8a8eeecd1de976fa`). The submodules are at `rooterberg` `85c1ae75` and `wycheproof` `b61843a9`.

Each of obligations 1 to 7 was audited on 2026-10-11 (the first obligation 1 run was interrupted and left no result) and again on 2026-10-17. Two cross-cutting audits ran alongside: ASSUME covers every premise of the final theorems, and AXIOMS covers axioms, escape hatches, guards and the inventory. Every audit result was then checked by a separate adversarial verifier that tried to refute it. Where a verifier disagreed with its audit, Claude checked the disputed points against the committed sources before writing this file; the statuses below are the corrected ones. The audits read central only. All Lean probes ran one module at a time against the published `LEAN_PATH` of `2cadb9be`. None of the audits ran `make verify`, a full `lake build`, ProVerif, mutation testing or `nix-collect-garbage`. An independent review of this file on 2026-10-17 found three major and ten smaller defects (among them an incomplete restatement of owner input 13, a Rust test command that skipped `beaconcrypt-core`, and an axiom check with no runnable program); they were fixed in a follow-up commit on this branch, which also adds the step 7 programs. A confirming review of that commit (`d95dd6dd`) approved it with four minor findings and three nits, all applied in the update of 2026-10-17.

How owner input 13 enters the statuses. Owner input 13 of the common-experiment plan asks the owner to confirm, per headline, the extension of approved games, idealizations and contracts to the headlines of the common experiment (restated in full under obligation 3 (b)). When this file was first written it had no recorded answer, so it conditioned every CE headline except the deterministic CE-R1 and CE-C3, with their LQ-F, D-ct and production forms, and the parts of obligations 2, 4, 5 and 7 met only through them were reported as closed in Lean and pending input 13. The owner approved input 13 as listed on 2026-10-17 (plan section 131), so those parts are now within the approved scope. Input 13 never conditioned the component theorems of items 1, 2, 4 and 5, which rest on the decisions and contracts approved for their own lines, nor the premise-free boundary equalities of item 7.

Summary:

- Obligations 1 and 6 are closed within the approved scope. For obligation 1, owner decision 6 (existential owner address, unread `chosenOwner`) and the one-sided form of T8 are still recorded as unconfirmed; confirming them cannot weaken a statement.
- Obligations 2, 4 and 5 are closed within the approved scope. The parts that are delivered only through the common experiment's headlines (for obligation 2 both directions, evolving and skipped keys and replay; for obligation 4 the target and session selection; for obligation 5 the common-experiment composition) were pending owner input 13, which the owner approved on 2026-10-17. The setup-carried `PublicDomain.available` contract that obligation 2 needed listed is now listed in both assumption ledgers.
- Obligation 3 is closed within the approved scope except for one scope point. Point (b), owner input 13, is approved; point (c), the per-operation selection, query and loss accounting, is now a table with Lean names (`doc/impl/deployment-experiment.md`, "Ideal operations (plan section 11, updated)"); point (a) is narrowed by O21, which states ten of the eleven session fields as an event of the experiment, to the root key: the owner acknowledges option R-a (root agreement only inside CE-A1's reductions) or chooses R-b or R-b′.
- Obligation 7 is closed within the approved scope, provided the owner accepts the reviewed transcriptions RT-01 to RT-20 as the last link from the Rust adapter to the Lean source programs. Its production headline forms now use only items of the approved input 13 list; `ReadWritable` at the production codec `codec'` is the approved CE-A1 contract at that instance of the codec parameter, which is Claude's reading of the approval (the owner may object).
- No assumption was added to close any obligation, and no component theorem was renamed into a closure.
- The pre-existing contracts carried by every final theorem's `Setup` (the X25519 public-domain availability laws and the `Pqxdh.Crypto` laws) and the `ReductionCaps` premise of the unbilled CE-A1 forms are now listed in the consolidated CE-13 assumption list and in the trust-boundary inventory.
- No repository Lean source contains `sorry`, `admit`, a custom axiom or another escape hatch. An exact reachability check finds only `propext`, `Classical.choice` and `Quot.sound` (at `2cadb9be` and again at `c6ee2307`). The maintained guard and policy gates are weaker than that check, so the AXIOMS audit stays partially closed; the trust-boundary inventory now records the dependency-layer axioms and the Lean 4.34 guard under-report.
- Item 8, the owner's final validation matrix, has not been run. None of the item 1 to 7 modules has ever been compiled together in one `lake build`.

| # | Obligation | Audit status | Verifier | Status after the decisions and fixes of 2026-10-17 |
| --- | --- | --- | --- | --- |
| 1 | Authenticated root theorem | closed within the approved scope | agrees | closed within the approved scope; owner decision 6 and the one-sided form of T8 still unconfirmed |
| 2 | Extract/HKDF composition | closed within the approved scope | agrees, with two qualifiers | closed within the approved scope: item 2's own theorems as before, and the CE-composed part (both directions, evolving and skipped keys, replay) under input 13, approved on 2026-10-17; the setup-carried `PublicDomain.available` contract is now listed |
| 3 | Common computational/symbolic experiment | closed within the approved scope, conditional | disagrees | closed within the approved scope except the root key of point (a): O21 states the other ten session fields as an event (central `c6ee2307`), and the owner acknowledges R-a or chooses R-b or R-b′; (b) input 13 approved; (c) the per-operation table is written (not yet reviewed) |
| 4 | CTX/AEAD lift to the global raw receive | closed within the approved scope | agrees | closed within the approved scope, including the target and session selection charged in the CE headlines (input 13 approved) |
| 5 | Evolving-chain source event | closed within the approved scope | agrees | closed within the approved scope, including the common-experiment composition (input 13 approved) |
| 6 | ProVerif coverage | closed within the approved scope | agrees | closed within the approved scope: the obligation's conditions hold; no unbounded coverage is proved |
| 7 | Production/source boundary | closed within the approved scope, conditional | agrees | closed within the approved scope if the owner accepts RT-01..RT-20; the production headline forms are within the approved input 13 list, with `ReadWritable` at the production codec read as the approved CE-A1 contract at that codec (Claude's reading) |
| ASSUME | Premises of all final theorems | partially closed | disagrees | closed within the approved scope; the CE-13 documentation defects are fixed |
| AXIOMS | Axioms, guards, inventory | partially closed | agrees | partially closed: the axiom property holds exactly (rechecked at `c6ee2307`), but guard coverage and the policy gate have gaps, and there has been no full build |
| 8 | Final validation matrix | not run (owner) | — | open; checklist below, with the mutation suite |

Owner decisions that remain open are collected in [Owner decisions and acknowledgements needed](#owner-decisions-and-acknowledgements-needed). The owner's checklist is [Item 8: the owner's validation checklist](#item-8-the-owners-validation-checklist).

## Basis, method and what Claude checked

Theorem names below are Lean declarations under `BeaconcryptCore.Computational` unless a namespace is given. Line numbers refer to the files at `2cadb9be` unless stated otherwise; central `c6ee2307` adds only the four O21 Lean modules and documentation, and the update of 2026-10-17 changes documentation only. Every theorem named here, except three, has an exact in-file `#guard_msgs` guard over `#print axioms` listing `propext`, `Classical.choice` and `Quot.sound`. The three exceptions: `PqxdhDeploymentIdealSlots.attach_detach` is guarded as depending on no axioms and `PqxdhDeploymentIdealLaterPool.onBase_view` as depending on `[propext, Quot.sound]` (both are under-reported lists, see the axiom scan), and `Pqxdh.INFO_PQ_ne_INFO_R` (`BeaconcryptCore/Model/Pqxdh/Primitives.lean:93`) has no guard. The exact walk of checklist step 7 covers all three. Every module named here is imported by `beaconcrypt-core/proofs/lean/BeaconcryptCore.lean` and listed in `beaconcrypt-core/proofs/reviewed-inventory.txt` with a matching SHA-256.

The audits' Lean evidence:

- Rebuilds. Single-module rebuilds from central's committed sources against the published `LEAN_PATH`, each through the coordination wrapper with `lean -j1 -M8000` and a 180 s timeout. All exited 0, and the oleans were byte-identical to the published ones. Counts: 28 item 1 modules, 56 item 2 and headline modules, 48 experiment, headline, registration and production modules, the 212-module item 4 closure, 5 item 5 key modules plus the root, and all 25 item 7 modules.
- Semantic comparison. 192 lake-built base modules of the item 5 closure that predate a later commit to their sources were rebuilt and compared semantically (lake-built oleans cannot be compared byte for byte; see the risks). All 192 were identical.
- Kernel replay. Every one of the 1,985 published oleans was kernel-replayed against its published imports. All 1,985 replayed with no failure, and a negative control failed as expected.
- Axiom reachability. An exact axiom-reachability walk was run from all 94,891 project constants. Checklist step 7 gives the program.
- Probes. Mechanical premise and closure probes were run on the headline, production and component theorems. ASSUME's set of 330 final theorems consists of every theorem named with a module-qualified name in the CE-13 computational column of `doc/proverif-source-scope.md`, in the CE-13 section of `doc/composition-assumptions.md` and in `doc/impl/production-headlines.md` (145 such names are theorems), all 200 theorems of the six `PqxdhDeploymentProduction*` modules at `2cadb9be`, and the item 2, 4 and 5 components that these theorems consume. Counts "of the 330 final theorems" below refer to this set. The CE-13 column also names 57 theorems by their bare name after a qualified one, among them the classical `PqxdhDeploymentHeadlineKeyTransfer.ce_kt` and `ce_kt_close`, `PqxdhDeploymentHeadlineCtColl.ct_coll_le`, `PqxdhDeploymentHeadlinePin.ce_or_pin_b2s`, `PqxdhDeploymentServerAuth.a1_sum` and the closed D-ct forms; they are outside ASSUME's set (the column cites 314 theorems in all), and their binders are covered by O3's binder scan of 1,597 theorems (obligation 3). The O21 theorems, added after the audits, have the premises of `ce_a1` (obligation 3 (a)).

The audits' working files are in the agents' registered scratch area on the shared machine. That area is transient and is not evidence of record, so every finding this handoff relies on is restated here.

Before writing, Claude checked the following against the committed sources:

- Owner input 13 of the common-experiment plan (`doc/impl/common-deployment-experiment-plan.md`, section 16) had no recorded answer. Sections 19 to 27 and the relayed owner decision records of 2026-10-07 to 2026-10-16 do not answer it, and the coordination messages of 2026-10-07 list it as pending. (The owner approved it as listed on 2026-10-17; plan section 131.)
- The plan section 22 cap loosening was still recorded as awaiting confirmation (also `doc/composition-assumptions.md`, CE-13 "Query bounds"). (Claude accepted it on 2026-10-17 under the owner's delegation as a bill-parameter choice; plan section 131.)
- The O21 change is a Claude decision (plan section 30). (O21 was then built and integrated: plan sections 129 to 131.)
- The current ideal-operations table (`doc/impl/deployment-experiment.md`, "Ideal operations") had only a "CE endpoint now" column, and the plan section 11 table that has selection, query and loss columns was stale. (The guide table now has the selection, query class and bill, and loss term of every operation; plan section 11 has a current Status column.)
- The X25519 public-domain contracts:
  - Definitions: `PqxdhServerStaticDhSource.PublicDomain` (`available : ∀ seed input, (joint.staticDh seed input).isSome = accepts input`) and `PqxdhPhase2GapDhSource.PublicDomain` (`available`, `nonzero`).
  - Placement: they are fields `serverDomain` and `beaconDomain` of `PqxdhServerAuthExperiment.Setup` (lines 70-71).
  - Use: the proofs of `PqxdhDeploymentKemTwoSided.kem_transfer_two_sided`, `PqxdhDeploymentIdealCompile.ideal_compile` and `PqxdhDeploymentIdealHandoff.ideal_world_view` use `serverDomain.available`: the reachability walk of checklist step 7, started from each of them, reaches the projection `PqxdhServerStaticDhSource.PublicDomain.available`. Started from item 2's `PqxdhRegistrationJointKemKeyTransfer.allIdeal_loss`, `PqxdhRegistrationJointKemPostSkeleton.opaqueBranch_shared` and `PqxdhRegistrationJointBeaconFinishOnce.slotGame_two`, it does not. The second check of step 7 prints these six results; Claude ran it in that form on 2026-10-17 against the published olean set.
  - Ledgers: they were recorded only in prose, at `beaconcrypt-core/proofs/trusted-boundary.md:449` ("native optional-DH availability law") and `doc/composition-assumptions.md:186` ("public optional availability"), and the CE-13 list of `doc/composition-assumptions.md` named only `prefixConsistent` and `setup.wiring` as setup-carried. (Both CE-13 lists now name them; update of 2026-10-17.)
  - Origin: they predate the handoff (commits `4136ea17` and `bf5cf596` of 2026-09-24, `Setup` in `aec2ee23` of 2026-09-30). They appear in the Milestone B design's `Setup` (`doc/impl/server-authentication-design.md`, "Every field is an existing functional contract").
- Rust. No production Rust, Go, bindings header, test or example file changed between the handoff basis `4d4ecf0c` and `2cadb9be`. Central's production Rust differs from `vcvio` (`8330cdef`, an ancestor of central, 977 commits behind) only by `5cbd76e3` (HB-95, sequence-one registration check) and `12d5dfcc` (extracted record wrapper): 4 files, +293/−60. Both commits predate the handoff, and neither is in `vcvio` or `main` (`61df2845`). `main` has two documentation-only commits not in central.
- `LEAN_PATH`. The published file exists, and all 42 of its prefixes are present. (Central `c6ee2307` has its own published `LEAN_PATH`, with 43 prefixes: the O21 prefix in front of the `d95dd6dd` file, which is byte-identical to the `2cadb9be` one.)
- Coordination. No lease or Lean slot was held when this file was written.

## The obligations

### 1. Authenticated root theorem

Status: closed within the approved scope (unchanged by the update of 2026-10-17). The verifier agrees. Owner decision 6 is still recorded as unconfirmed (see the remaining gaps); confirming it cannot weaken a statement.

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
- No document named T5/T8 as the item 1 closure, and several passages called item 1 open. (Fixed on 2026-10-17: the passages carry update notes that name T5 and T8, and this file is the record of the closure.)

### 2. Extract/HKDF composition at the actual joint sampler

Status: closed within the approved scope. Item 2's own theorems are closed within the approved scope. The part of the obligation that is delivered only through the common experiment (see qualifier (ii)) was pending owner input 13, which the owner approved as listed on 2026-10-17. The setup-carried `PublicDomain.available` contract (qualifier (i)) is now listed in both assumption ledgers. The audit and its verifier had reported "closed within the approved scope, with two qualifiers"; the review of this file showed that qualifier (ii) was too narrow, and the owner's answer to input 13 settles it.

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
- (ii) The hybrid starts from the experiment's real deployment game, and records enter only through the CE composition (`records_close`, `ce_kt_sum` and the record-consuming headlines). So the obligation's full list (both directions, evolving keys, skipped keys, replay) is met only by CE headlines. Owner input 13 asks the owner to confirm, for CE-KT, the R1 Extract-ROM, the HMAC-PRF, Extract on `uniform32`, `SourceFullCorrect`, `prefixConsistent` and ML-KEM IND-CCA with its correctness error and `FunctionalDecapsulation`; for the record headlines it adds the BLAKE2b random oracle and the AEAD games. The 2026-10-06 item 2 decisions settle this only in part (`doc/impl/extract-composition-plan.md`, section 16). They accept the HMAC-PRF and Extract on a uniform 32-byte key as ordinary primitive games without a scope limit, but they extend R1 only "to this line", the item 2 line, and allow `SourceFullCorrect` only "as a premise of T7/T8"; and input 13 still lists all of these for CE-KT. The common-experiment plan reads them as inherited by the experiment (its section 2 table and section 17), but it still lists them under input 13 for confirmation. Until the owner answered input 13, this part of obligation 2 was closed in Lean and pending, as obligation 3 was. The approval of 2026-10-17 lists, for CE-KT, exactly these items and, for the record headlines, the BLAKE2b random oracle and the AEAD games, so this part is now within the approved scope. The basis of `SourceFullCorrect` is older than the item 2 decision: it is a premise of the owner-approved Milestone B Server-authentication theorem (`doc/impl/server-authentication-design.md`, section 3) and the permanent functional contract of the HB-84 chain line (`trusted-boundary.md`, HB-84 entries), and the item 2 decision extends it to T7 and T8.

Remaining gaps:

- Permitted reveals and descendant-only compromise hold only vacuously in the classical core, which has no reveal command. They are moot, not discharged. LQ-F covers a post-run reveal of identity seeds and X25519 scalars only, for confidentiality.
- There is no computational root-secrecy statement. The uniform root appears only as an intermediate hybrid world.
- Item 2's own theorems are stated over source14 (registration). Records enter only through the CE composition, by design, which is why qualifier (ii) applies.
- The hybrid is per target, summed exactly. It is not a single all-sessions hybrid.
- Everything holds in the random-oracle model of the slice. No theorem relates the R1 table to production HKDF-Extract.
- Bills count queries and coins, not running time.

### 3. Common computational/symbolic experiment

Status: the Lean content is verified. The verifier's corrected status, which Claude confirmed against the sources, was closed within the approved scope pending the owner's acknowledgement of three points (a) to (c) below. The audit had named only (a) and the section 22 caps; the verifier added (b) and (c) and showed that the caps do not block closure. After 2026-10-17: (b) is approved, (c) is delivered as a per-operation table, and (a) is narrowed by O21 to the root key, which needs the owner's acknowledgement of option R-a or a choice of R-b or R-b′. The obligation is therefore closed within the approved scope except for that one point.

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
  - Update of 2026-10-17 (O21 built and integrated, central `c6ee2307`; plan sections 129 to 131): `PqxdhDeploymentSessionAgreement.ce_a1_agreement` states ten of the eleven fields, all but the root, as an event of `PqxdhDeploymentSecrecy.game` at identity index 0, with the premises and bound of `ce_a1` (billed form `ce_a1_agreement_billed`, deterministic handle lookup `lookup_agree`, production forms in `PqxdhDeploymentProductionSessionAgreement`). On the support at index 0 the new event coincides with CE-A1's (`noAgreement_iff`), so it adds no probability content: what it adds is that whenever the public pinned match holds, the ten fields read from both parties' final states agree (the associated data, the pinned key ID, the identity key and the consumed registration ID among them). The rows A1-delayed, S2b-initial, A1, s2b-A1, b2s-A1, encoding-A1, position 1 of s2b-C1, and now also SSX-b2s-origin 3194 and SSX-s2b-origin 3195 stay partial, with only the root, the assigned key ID and the payload symbolic-only.
  - What remains is the root: the experiment keeps no labelled Beacon root, so root equality is not a readout of its outcome, and root agreement holds only inside the ServerAuth runs of CE-A1's reductions `R_c`. Options (none built): R-a (recommended), accept the root as inside `R_c` only; R-b, an extended game that logs each Beacon's root, with an erasure lemma and a state-carrying coupling of the CE-A1 chain (estimated 12 to 30 agent-days); R-b′, a kernel-lineage event on the unchanged game, which needs the same coupling. The application payload and the assigned key ID are outside the eleven fields; their agreement is an optional follow-up (6 to 10 agent-days). This is the one point of obligation 3 that needs an owner decision.
- (b) Owner input 13 (`doc/impl/common-deployment-experiment-plan.md`, section 16, item 13) had no recorded answer when this file was first written. The owner approved it as listed on 2026-10-17 (plan section 131), with the same lists as below and `DecoderAgreement` for the record headlines. It asks the owner to "confirm the scope extension to CE of each of the following, per headline":
  - CE-A2, CE-A2pub, CE-R1': joint Ed25519/X25519 weak EUF (`PqxdhJointIdentity`), and `shortRejects` with `setup.wiring`.
  - CE-A1: Gap-DH, the classical programmable R1 Extract-ROM, the classical programmable BLAKE2b random oracle, joint weak EUF, the record and schedule loss terms of `PqxdhRegistrationR1Authentication.generated_authentication` (the plan requires their primitive games to be listed in CE-13), and the premises `X25519ClassLaw`, `X25519ScalarSpread`, `SourceFullCorrect`, `HasAttachedVerificationAdapter`, `ReadWritable`, `Phase2ReadBack` and `FrameReadBack`.
  - CE-KT: ML-KEM IND-CCA with its correctness error and `FunctionalDecapsulation`, the R1 Extract-ROM, the HMAC-PRF, Extract on `uniform32`, `SourceFullCorrect`, and `prefixConsistent` inside `setup`.
  - CE-OR, CE-UKS, CE-APP, CE-LOR: everything above, plus the BLAKE2b random oracle, the modified-nonce AEAD IND$ and INT-CTXT games of the CTX components, and whatever item 4's receive-side lift needs (for example `DecoderAgreement`).
  - CE-R1, CE-C3: nothing (deterministic).
  - The LQ-F, D-ct and production forms are forms of these headlines and carry the same items. The production forms add `ReadWritable` at `codec'`.
  - Each headline family uses its items unconditionally, as explicit premises or reduction advantages. The codec contracts of plan section 19 answer input 14, not input 13.
  - Since 2026-10-17 the CE-13 section of `doc/composition-assumptions.md` presents every headline family as within this approved list, and the production forms' `ReadWritable` at `codec'` as the approved CE-A1 contract at that instance (Claude's reading, which the owner may correct). The plan says that these extensions are used only after approval (section 2 table, line 88, and section 17). Its section 17 also says that item 2's R1 extension, Extract on `uniform32` and `SourceFullCorrect` are "inherited exactly as the owner approved them on 2026-10-06". Of those decisions, the R1 extension is scoped to the item 2 line and `SourceFullCorrect` to T7/T8, and input 13 still lists these items for CE-KT and CE-A1 (see obligation 2, qualifier (ii)). The sentence "every item below was approved before (2026-10-06, 2026-10-07)" in the CE-13 section of `doc/composition-assumptions.md` had no owner record behind it for these extensions; it now cites the approval of 2026-10-17. They were never hidden: each is an explicit premise or a named advantage.
- (c) The handoff asks for every ProVerif ideal operation's "selection/query/loss accounting". Lean proves selection globally (`split_named`) and query bills globally (`headline_bills`, `later_headline_bills`). The per-operation table was not current: the plan section 11 table still said "Planned" for O5-O9, O18 and O20 and "CE-12" for O21, and the updated guide table gave only the endpoint. Since 2026-10-17 the guide table (`doc/impl/deployment-experiment.md`, "Ideal operations (plan section 11, updated)") gives, for each of O1 to O27, the CE endpoint, the selection (for example `split_named`, `PqxdhDeploymentKemTwoSided.split_create`, `PqxdhDeploymentTargetRange.range_game_create`, the record hops of `PqxdhRecordLiftChainLift.chain_lift`), the query class with its bill theorem (for example the `TargetBills` fields of `target_bills`, `a1_bills_all`, `later_headline_bills`) and the loss term (`kemLoss`, `slotLoss`, `authLoss`, `recLoss`, `beta`, `a1Term`, `a2pubTerm`, `injTerm`, `ctCollEps`), with Lean names; plan section 11 has a current Status column. The table has not been independently reviewed yet.
- Not blocking: the plan section 22 cap loosening is a choice of bill parameters. The BLAKE2b cap is `qHash + S + R + qTest + qFresh`, and the coin cap is `qCoin + qTest + qFreshBytes`. Every bill is proved at these sound caps. Claude accepted it on 2026-10-17 under the owner's delegation of 2026-10-07 (plan section 131).

Other gaps, all approved partial rows or disclosed exclusions:

- Root secrecy as `attacker(root)` is not computational; CE-RG is not built.
- These are symbolic-only or not claimed: O13 cross-object builds (CE-M is not built), multi-test-session LOR, plaintext-linked unknown key share, `INITIAL_SECRET`, several Server objects, Beacons pinned to other key IDs, and any authentication in LQ-F.
- Some links rest on prose or code inspection: exhaustiveness of the injective forms, key-ID uniqueness, "every published record is a production `Sent`", D2 getter derivability, and the whole symbolic map (by design, input 18).
- No single Lean witness shows that the full premise bundle is jointly satisfiable. `PqxdhServerAuthJointWitness.joint_witness` lacks `HasAttachedVerificationAdapter`, `shortRejects` and `KemBound` in one instance, and nothing covers the production codec.

### 4. Typed CTX/AEAD results lifted to the global adaptive raw receive interface

Status: closed within the approved scope. The verifier agrees and found citation and counting defects only. The obligation also asks to "charge target/session/record selection". Record selection is charged inside the lift (its hops). Target and session selection are charged only in the CE headlines (`PqxdhDeploymentHeadlineChain.split_named`); that part was pending owner input 13 and is within the approved scope since the owner approved input 13 on 2026-10-17.

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

Status: closed within the approved scope. The verifier agrees. The obligation also asks for the "common-experiment composition", which exists only in the CE headlines; that part was pending owner input 13 and is within the approved scope since the owner approved input 13 on 2026-10-17.

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
- `trusted-boundary.md:876` and `formal-verification-analysis.md:4190` named only L1, L2 and E19 as open for exact-far, while the ledger also lists L3, L4, L5 and the global relation. This was a minor source-scope overclaim in two reference documents, not an overclaim of a verdict; both sentences were corrected on 2026-10-17.

### 7. Production/source boundary

Status: closed within the approved scope, on condition that the owner accepts the reviewed transcriptions RT-01 to RT-20 as the final link from the unextracted Rust adapter (`beaconcrypt/src`) to the Lean source programs. If the owner instead requires the seven proposed mechanical pins (PB-D1, PB-SURFACE, PB-CHECKS, PB-CAP, PB-TRANSITION, PB-AD, PB-GHOST), obligation 7 stays partially closed until they exist with mutation rows. None exists, by lane decision D-4, not by owner decision. The verifier agrees. The boundary equalities need no answer to owner input 13. The production headline forms carry the conditions of the CE headlines; they were pending input 13 and are within the approved list since 2026-10-17. Input 13 lists `ReadWritable` for CE-A1 without naming a codec; the production forms instantiate the codec parameter at the production codec, where `ReadWritable codec'.frameWrite codec'.frameRead` is a joint condition on the abstract frame writer and the production decoder, carried and not proved. Claude reads the approval as covering that instance (plan section 131); the owner may object.

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

- The Rust-to-Lean link is reviewed transcription, inside the adapter review units OR-01 to OR-18 of `trusted-boundary.md`. RT-01 to RT-20 were listed only in `doc/impl/production-boundary-ledger.md`; since 2026-10-17 `trusted-boundary.md` lists them too (section "Completion fixes of 2026-10-17").
- Associated data has no dedicated theorem; it is carried by the record equalities and RT-17.
- Root (`PqxdhBoundaryRoot`) and rollback (`PqxdhBoundaryRecordReceiveState`) are leaf modules, so `step_exact` rests on PB-01, 02, 03, 05, 06, 07, 08 and 09.
- The acceptance and birth joins are thin unfoldings of the experiment's existing transcriptions. They are new equalities, not renamed theorems, but they add no evidence about the Rust code.
- Replay and rollback are support facts, not equalities.
- `ReadWritable` is not a plan section 19 codec law. Its use at the production codec falls under owner input 13, approved on 2026-10-17 (Claude's reading for the production instance, above).
- No claim is made about any deployment that uses only the C, Go or Python bindings, whose Server is persistence-wrapped.

## Assumption ledger

### Hidden-assumption finding

**No assumption was added to close obligations 1 to 7.** Every premise of the final theorems is an explicit binder or a field of an argument structure: there is no `variable` instance, `Fact` or global hypothesis, and no component theorem was renamed. One contract that is a field of the `Setup` argument, and so ambient to every final theorem, was nevertheless missing from the consolidated CE-13 assumption list (both CE-13 lists name it since 2026-10-17):

- `Setup.serverDomain.available` (`PqxdhServerStaticDhSource.PublicDomain`): X25519 static-DH availability depends only on a public predicate of the peer encoding, not on the secret seed.
- `Setup.beaconDomain.available` and `Setup.beaconDomain.nonzero` (`PqxdhPhase2GapDhSource.PublicDomain`). The `nonzero` law is redundant at the instance that `Setup` fixes: `beaconDomain` is a `PublicDomain` of `PqxdhJointGapDh.sourceInterface`, whose DH function `PqxdhJointGapDh.sourceScalarDh` returns `none` on an all-zero output, so every `some` value is nonzero by definition. It is still used, by `PqxdhPhase2DhMetadata.selected_nonzero` (`PqxdhPhase2DhMetadata.lean:21`).

Every final theorem quantifies over a `Setup` that carries these fields, and the experiment's KEM-transfer and ideal-world equalities use `serverDomain.available`. The laws are true of clamped X25519 as libsodium implements it: the output is all-zero exactly for small-order peers, independent of the scalar. They predate the handoff and are part of the Milestone B `Setup` design. They are recorded in prose ("native optional-DH availability law", `trusted-boundary.md:449`; "public optional availability", `composition-assumptions.md:186`), but no ledger named them, and the CE-13 list said that `setup` carries only `prefixConsistent` and `wiring`. ASSUME first classified this as a hidden contract. Its verifier reclassified it as an approved but under-documented contract, and Claude agrees after reading the sources. The CE-13 sections of `doc/composition-assumptions.md` and `trusted-boundary.md` list it since 2026-10-17.

Two further documentation gaps of the same kind, also fixed in both CE-13 lists on 2026-10-17:

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
- `ReadWritable codec.frameWrite codec.frameRead`: a restricted writer totality. It is the approved message-model premise of the first-record line (Milestone B and audit remediation C), not a section 19 law. Its use in the experiment is approved by input 13 (2026-10-17); at `codec'` it is that contract at the production instance (Claude's reading, obligation 7).
- `SourceFullCorrect setup.source setup.hmac`: a premise of the owner-approved Milestone B Server-authentication theorem (`doc/impl/server-authentication-design.md`, section 3) and the permanent functional contract of the HB-84 chain line, so the component theorems of items 4 and 5 (`record_lift`, `record_auth_lift`, `chain_lift`) rest on that approval; the item 2 decision of 2026-10-06 extends it to T7 and T8, and input 13 lists it for CE-A1 and CE-KT.
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
- The environment declares 33 axiom constants, including Aeneas opaque-type and spec axioms and `native_decide` axioms of Hax `CoreModels`. None is reachable. `trusted-boundary.md` lists them since 2026-10-17 (section "Completion fixes of 2026-10-17").
- On 2026-10-17 Claude ran the step 7 walk again at central `c6ee2307` through the coordination wrapper, against its published olean set: 95,086 roots, 121,963 constants reached, 0 unresolved, only the three standard axioms, and the six `SERVER-DOMAIN` results unchanged (18 s). A probe that compared the exact sets of the 118 theorem constants of the four O21 modules with Lean's lists found no difference, so the count of under-reporting guards stays 20.
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
- The dependency layer. The trusted Aeneas and Hax libraries declare axioms, and no ledger recorded this; `trusted-boundary.md:112` is silent on that layer. (Recorded since 2026-10-17, with the exact reachability result and the Lean 4.34 guard caveat, in the section "Completion fixes of 2026-10-17" of `trusted-boundary.md`.)
- The full build. The tree has never been checked in one `lake build`.

## What is explicitly not claimed

- Nothing about the persistence-wrapped Server surface of the C, Go and Python bindings, and nothing about persistence, snapshots or restoration.
- No authentication, origin, binding or unknown-key-share claim in the later-quantum mode LQ-F. LQ-F claims confidentiality only (CE-KT-L, CE-APP-L, CE-LOR-L).
- No SSX-origin full-response equality (rows SSX-b2s-origin 3194 and SSX-s2b-origin 3195). Exact full-response equality is false under X25519 encoding aliases; the experiment uses lookup by session handle instead. Since O21, ten of the eleven session fields are an event of the experiment; the root, the assigned key ID and the application payload are not (obligation 3 (a)).
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

Recorded on 2026-10-17 and no longer open:

- Owner input 13 (plan section 16) is approved as listed: the headlines may use the primitive games and contracts already approved for their component lines (plan section 131 gives the list per headline). This settles the pending parts of obligations 2, 3 (b), 4, 5 and 7's production forms.
- The two shared dependency worktrees are restored and protected (owner's choice "Restore + protect").
- The plan section 22 cap loosening is accepted, as a Claude decision under the owner's delegation of 2026-10-07, as a bill-parameter choice.
- The listing that this file asked for (the setup-carried X25519 `PublicDomain` contracts, the model-level reading of the `Pqxdh.Crypto` laws, `ReductionCaps`) is done in both assumption ledgers. These are pre-existing contracts, so no owner decision is needed; the owner may review the listing.
- The per-operation selection, query and loss table of obligation 3 (c) is written; the owner may review it.

Still needed:

1. Obligation 3 (a), the root key of the initial response: acknowledge option R-a (root agreement only inside the ServerAuth runs of CE-A1's reductions, recommended), or choose R-b (an extended game that logs Beacon roots, 12 to 30 agent-days) or R-b′ (a kernel-lineage event on the unchanged game, needing the same coupling). Optionally schedule the payload and assigned key ID follow-up (6 to 10 agent-days). This is the only open point of obligation 3.
2. Accept RT-01 to RT-20 as reviewed transcription for obligation 7, or require the seven PB-* pins. The pins would mean Rust test changes and therefore mutation testing.
3. Confirm owner decision 6 (existential owner address in `AcceptOrigin.Protected`, unread `chosenOwner`) and the one-sided form of T8 (item 2 plan input 5). Neither can weaken a statement.
4. Not blocking: confirm or correct Claude's reading that the approval of `ReadWritable` for CE-A1 covers its instance at the production codec `codec'`.
5. Decide whether any owner-optional extension (CE-M, CE-RG, multi-test-session LOR, which is plan input 7's unanswered second question) is wanted.
6. Decide the merge basis. Central contains `5cbd76e3` (HB-95) and `12d5dfcc`, and `vcvio` and `main` do not; the owner handles HB-95.
7. Run item 8, including the complete mutation suite (step 8), on the exact merge.
8. Decide whether the step 7 programs should become maintained gates and whether `check-lean-policy` should also reject `native_decide`, `decide +native`, `implemented_by`, `extern`, `unsafe` and `opaque`; either is a separate, owner-approved change.

## Item 8: the owner's validation checklist

Item 8 is the owner's. No agent has run any part of it on a final merged result. The checklist follows `AGENTS.md` and item 8 of the 2026-10-06 handoff. Run it on the exact merge that will be published, in a fresh clone, not in a machine-local worktree or against an olean overlay: `git clone <origin URL> <clone>`, then `git -C <clone> checkout <exact merge commit>` and step 1, so that the sources, the submodules and every dependency come from the remote and nothing comes from `/tmp`.

Basis:

- The tip that will actually be merged. When this file was first written that was central `codex/full-proof-composition` at `2cadb9be1b0575b7fb25b295c9df83ce3c94919d`; central is now at `c6ee2307615f9ba4209f01ab1bcda7ee41efebce` (this handoff at `d95dd6dd`, then the four O21 Lean modules), and the update of 2026-10-17 is on branch `codex/completion-fixes-2026-10-17` (documentation only) until it is integrated. `vcvio` (`8330cdef`) is an ancestor of central and fast-forwards to it. Merging into `main` (`61df2845`) is a true merge, and `main` has two documentation-only commits that central lacks.
- The published `LEAN_PATH` of central `c6ee2307` is `/tmp/bc-coord/leanpaths/c6ee2307615f9ba4209f01ab1bcda7ee41efebce.leanpath`, the value of `coord.sh leanpath current`: 43 prefixes, the O21 prefix in front of the 42 prefixes of the `2cadb9be` file (SHA-256 `3c3aa07d8889f6a0ae1bc97a9e92d18cbcc709d5e3032db9a1a6430fd49d0577`), SHA-256 `e163c59613af657b957d5db36cdc15d9d6dffce15bd7b39bfaff0b6d64ee6f73`.
  - It is a transient machine-local symlink mosaic over 115 build directories under `/tmp`, kept only by the access-time refresh.
  - It reproduces the audits' per-module probes and nothing else. Item 8 must not depend on it.
  - The superseded `LEAN_PATH` files beside it are older trees; use none of them.
- Dependency worktrees. The published `LEAN_PATH` resolves the dependency oleans (Mathlib, VCVio, Aeneas, Hax, batteries and the other packages) into the shared worktree `/tmp/beaconcrypt-server-auth-ctx-observer-integration` and 151 module oleans into `/tmp/beaconcrypt-server-auth-common-integration`. The `/tmp` cleaner had deleted 522 and 575 tracked files of these worktrees, among them `beaconcrypt-core/proofs/lean/lakefile.toml`, `lean-toolchain` and `patches/`. On the owner's decision of 2026-10-17 Claude restored their committed contents with `git checkout` (their `.lake` trees untouched; both have an empty `git status`), and the 12-hourly access-time refresh now covers them and central. They remain shared, read-only and machine-local: the fresh clone must fetch its own dependencies (lake reads `beaconcrypt-core/proofs/lean/lake-manifest.json`, and the Aeneas and Hax patches are in `beaconcrypt-core/proofs/lean/patches/`) and must not reuse these trees or their `.lake`.

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
   - `check-proverif`: the legacy roster of 35 scenarios in parallel, plus four prerequisite groups of the target that are not roster scenarios: transcript fidelity (`check-proverif-transcript-fidelity`, also run alone in step 4), live material (5 targets), private application (3 targets) and the KEM-controller authentication gate (1 target);
   - `check-proverif-fs`: the serial free-schedule group;
   - the eleven extension targets;
   - `extract-lean`;
   - `check-lean`: dependency patches, `check-lean-policy`, `check-lean-root`, `check-lean-panic-freedom`, then `lake --rehash build` of all 1,989 modules at `c6ee2307` (1,985 at `2cadb9be`), which is the exact-merge full build;
   - `check-inventory`.

   Afterwards `git status --short` must show no drift in `beaconcrypt-core/proofs/pro-verif/extraction` or the generated Lean paths. These are the paths `make check-generated` checks, but that target reruns `verify`.
6. Inventory: run `make -C <clone>/beaconcrypt-core check-inventory SHELL=bash` separately inside the proof shell, as `AGENTS.md` asks.
7. Forbidden-placeholder and axiom scans, beyond `check-lean-policy`. Both programs are given in full under "Step 7 programs" below.
   - The source scan. It blanks comments, strings and character literals in every Lean file tracked under `beaconcrypt-core/proofs/lean` (its default file list is `git ls-files '*.lean'` run in that directory; the 18 tracked historical stage copies under `doc/impl/handover/milestone-b/stages` can be scanned by passing them as arguments) and reports `sorry`, `admit`, `sorryAx`, `axiom`, `native_decide`, `decide +native`, `ofReduceBool`, `ofReduceNat`, `implemented_by`, `extern`, `unsafe`, `opaque`, `partial def`, `csimp`, `#exit`, `#eval`, `run_cmd`, `run_tac`, `run_elab`, `addDecl`, `import Lean`, `debug.` options, `skipKernelTC`, `trustCompiler`, `allowUnsafe` and every non-local `macro`, `macro_rules`, `syntax`, `elab`, `elab_rules`, `notation`, `infix`, `infixl`, `infixr`, `prefix` or `postfix` command that starts a line, after optional indentation, attributes, an `open … in` or `set_option … in` prefix, `private` or `protected`, and `scoped` with or without a namespace (a doc comment on the same line is blanked first). Commands with `local` are not reported. Expected at `c6ee2307`: `LEAN-SCAN files 1989 hits 0` and exit 0 (at `2cadb9be`: 1985 files). Any hit exits 1. The pattern was widened on 2026-10-17 after the confirming review found that the first version missed indented, `scoped[…]`, doc-commented and `open … in` commands; the widened program reports all six such forms of the review's control file, still reports every token of the dirty control, and gives 0 hits on central.
   - The exact axiom walk, on the full build's output. It imports every module and follows the constants used by every type, value (opaque values included) and constructor, from every `BeaconcryptCore` constant, without Lean's precomputed axiom data. It fails unless every name resolves and the axioms reached are only `propext`, `Classical.choice` and `Quot.sound` (a subset check; the printed list shows the actual set). Do not rely on `#print axioms` alone, because of the Lean 4.34 under-report described above. Its second check reproduces the `serverDomain.available` usage finding. Expected output at `c6ee2307`, with exit 0 (the counts change only if the merge changes Lean sources; at `2cadb9be` the first line read `AXIOM-WALK roots 94891 reached 121768 unresolved 0`):

     ```text
     AXIOM-WALK roots 95086 reached 121963 unresolved 0
     AXIOM-WALK axioms [Classical.choice, Quot.sound, propext]
     SERVER-DOMAIN PqxdhDeploymentKemTwoSided.kem_transfer_two_sided true
     SERVER-DOMAIN PqxdhDeploymentIdealCompile.ideal_compile true
     SERVER-DOMAIN PqxdhDeploymentIdealHandoff.ideal_world_view true
     SERVER-DOMAIN PqxdhRegistrationJointKemKeyTransfer.allIdeal_loss false
     SERVER-DOMAIN PqxdhRegistrationJointKemPostSkeleton.opaqueBranch_shared false
     SERVER-DOMAIN PqxdhRegistrationJointBeaconFinishOnce.slotGame_two false
     ```

8. Mutation testing (required). The item 1 to 7 work changed no production Rust: `beaconcrypt/src`, `beaconcrypt-core/src`, the Go files, `beaconcrypt/bindings.h`, tests and examples are identical between `4d4ecf0c` and `2cadb9be`, and `c6ee2307` adds only Lean and documentation. But central's production Rust differs from `vcvio` and `main` by `5cbd76e3` (HB-95, the sequence-one registration check) and `12d5dfcc` (the extracted record wrapper): `beaconcrypt/src/beacon.rs`, `beaconcrypt/src/ratchet.rs`, `beaconcrypt-core/src/record.rs` and `beaconcrypt-core/src/lib.rs`, +293/−60. Publishing central onto either base is therefore a production Rust change, and the `AGENTS.md` mutation requirement applies: run the complete configured `cargo mutants --workspace --jobs 6` (configuration `.cargo/mutants.toml`) on the exact merge and fix every missed or timed-out viable mutant. The last complete run had 1,173 cases in 36 min (`doc/impl/staged-verification-record.md`); it predates `5cbd76e3` and `12d5dfcc`, so it is not evidence for them.
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
    r"|^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:(?:open|set_option)\b[^\n]*?\bin[ \t]+)?(?:(?:private|protected)[ \t]+)?"
    r"(?:scoped(?:\[[^\]]*\])?[ \t]+)?(?:macro|macro_rules|syntax|elab|elab_rules|notation|infixl?|infixr|prefix"
    r"|postfix)\b", re.M)

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
| Full `lake --rehash build` | Unmeasured. The last full build (`edc701e7`, 2026-10-01) had 4,728 lake jobs for 1,186 handwritten Lean files; there are now 1,982 handwritten and 7 generated at `c6ee2307` (1,978 at `2cadb9be`), so expect proportionally more. Single-module compiles take 3 to 7 s; sequential rebuild samples ran 5 to 6.5 s per module including queueing (192 modules in 1,219 s), so about 3 h on one worker for the 1,989 project modules, less in parallel. Dependency builds (Mathlib v4.34.0, VCVio, Aeneas and Hax with the repository patches) come on top unless their outputs are reused. | Unmeasured for a full build. A single Lean check peaks at 3.97 GiB RSS on average and 4.32 GiB at most, mostly shared olean page cache. The coordination class for an 8-worker `lake build` is an 8,192 MiB estimate. Heartbeat limits of one full build are unmeasured. | `doc/impl/handover/pause-2026-10-01/integrated-evidence/beaconcrypt-common-integration-after-make.json` (job count); machine measurements (RSS, rebuild timings) |
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
- **Stale `LEAN_PATH` files not retired.** 88 superseded `LEAN_PATH` files were pinned beside the current one at `2cadb9be` (90 beside the `c6ee2307` file on 2026-10-17). They could not be retired because the protocol retires a superseded file only after the other agent acknowledges the newer integration, and Codex never did: Codex has been inactive since 2026-10-09 23:39, and 54 Claude requests and integration announcements await acknowledgement. They keep old overlay directories alive and must not be used. The mirrors also link `.olean` and `.ilean` independently, so editor positions can mislead, for example for `PqxdhRegistrationScheduleSurface`.
- **HB-95 and the merge basis.** `origin/main` (`61df2845`) and `vcvio` (`8330cdef`) lack `5cbd76e3` (HB-95, the sequence-one Beacon registration check, `beacon.rs:467-469`) and `12d5dfcc`. Every PB anchor, RT review and Rust spot check was made against central's Rust. A final merge onto a base without them would invalidate the PB-06 and PB-11 anchors. The owner handles HB-95.
- **/tmp volatility.**
  - The systemd-tmpfiles cleaner deleted 18 tracked central files and 2,041 submodule files; they were restored on 2026-10-16.
  - It also deleted 522 tracked files of the shared dependency worktree `/tmp/beaconcrypt-server-auth-ctx-observer-integration`, including `beaconcrypt-core/proofs/lean/lakefile.toml`, `lean-toolchain` and `patches/`, and 575 of `/tmp/beaconcrypt-server-auth-common-integration`. Their `.lake` outputs, which supply dependency oleans of the published `LEAN_PATH`, are intact. On the owner's decision of 2026-10-17 their tracked files were restored from their committed contents, and the access-time refresh now covers them (see the item 8 basis).
  - Committed documents contain about 16,400 `/tmp` references in 377 files. The 21 production receipts hold about 1,540 of them, and their evidence will not survive the cleaner.
- **Axiom gate.** In Lean 4.34, guards can under-report (see above), and `check-lean-policy` does not reject `native_decide`, `implemented_by`, `extern`, `unsafe` or `opaque`. A future change that reaches a dependency axiom through a structure field could pass every guard and the gate. The step 7 programs check both properties for the owner's run, but they are not maintained gates; committing them as reviewed checks would be a separate, owner-approved change.
- **ProVerif margins.** The fs group uses 96.5% of its time budget, and A1 uses 96.7% of the memory cap. The general-registration checker changed after its last solver run; its expected verdicts are AST-identical. The complete configured gate has never run in one invocation.
- **Stale Lean docstrings.** Fixing the stale docstrings listed below changes oleans. Any such edit before item 8 needs those modules and their dependents re-checked, and the inventory re-hashed.
- **No joint-satisfiability witness for the full premise bundle in Lean.** The production codec's satisfiability is a prose argument (`doc/impl/production-headlines.md:80`).

## Documentation defects found by the audits and their resolution

Most of these understate what Lean proves. The exceptions, which said slightly more than the sources support, were the two exact-far lines (obligation 6), the incomplete CE-13 assumption list with its approval sentence, the quoted under-reported axiom lists and the HB-111 wording. None claims a Lean statement that does not exist. Line numbers are at `2cadb9be`. The update of 2026-10-17 fixed every defect in a document that Claude maintains, by an in-place correction marked with its date or, for paragraphs written by Codex or before the coordination rules, by a superseding note in a new section at the end of the same file; it left the published Lean modules and the dated records unchanged. The first version of this file already fixed `doc/impl/handover/README.md`, which named the 2026-10-01 pause handoff as current.

- Assumption lists (fixed):
  - `doc/composition-assumptions.md`, CE-13 section: the setup bullet names the `PublicDomain` laws and the `Pqxdh.Crypto` laws with their model-level reading and that no final statement reaches `decap`, `encap`, `kemPub` or `decap_encap`; the CE-A1 bullet and the query bounds name `ReductionCaps`; the approval sentence cites the owner's answer to input 13; the cap loosening cites the decision of 2026-10-17; `ReadWritable`'s provenance (Milestone B and audit remediation C, then input 13) and the restricted writer totality of the CE-3 paragraph are stated.
  - `trusted-boundary.md:918`: the enumeration now names the public-domain laws (HB-118), the `Pqxdh.Crypto` laws (LA-10) with their model-level reading and `ReductionCaps`.
  - The T8 paragraphs (`trusted-boundary.md:910`, `composition-assumptions.md:226`): they name `prefixConsistent.ratchetPrefix` and the `Pqxdh.Crypto` laws that T5 and T8 use.
  - Exception (b) of the LQ-F reveal profile (`composition-assumptions.md:33`, `trusted-boundary.md:916`): the owner's wording "PQ-key parse" is kept, with a note that the rejecting Rust step is the KEM admission inside `encapsulate` (`server.rs:373`).
- `beaconcrypt-core/proofs/trusted-boundary.md` (fixed; inventory digest rehashed):
  - Lines 843, 847 and 856 (written by Codex) still call the item 7 joins pending; a superseding note and entries for the 14 item 7 modules that had none, and for the O21 modules, are in the new section "Completion fixes of 2026-10-17".
  - RT-01 to RT-20 are listed there.
  - Lines 896 and 904: update notes say that item 2 and the common experiment supplied the open joins.
  - Line 876: the exact-far sentence names L3, L4, L5 and the global source relation too.
  - Line 112 (written before the coordination rules): the new section records the 33 dependency-layer axiom constants, the exact reachability result (none reachable), the policy gate's limits and the Lean 4.34 guard under-report with the 20 affected theorems.
- `doc/formal-verification.md` (fixed): the HB-111 sentence of line 5 says that HB-111 is not the item 1 theorem; lines 25, 58 and 134 carry update notes; a new last section summarizes the common experiment and points to this file; lines 48 and 55 (written by Codex) are superseded by that section. `doc/composition-assumptions.md:13` has the same HB-111 note.
- `doc/formal-verification-analysis.md` (fixed): line 4752 (item 1 open) and lines 5206 and 5216 (origin and binding open) carry update notes; the S4 sentence on the zero CTX refusal names `PqxdhRecordLiftProtocolHistory.program_fresh` and `PqxdhRecordLiftCtxHybrid.allReal_bare`; line 4190 names the remaining exact-far obligations; the CE-13 summary no longer says "one entry per ProVerif target"; the O21 section says that O21 is integrated; a new last section records the decisions of 2026-10-17 and what stays open, including that "end to end" in the item 7 heading means up to the Lean source programs.
- `doc/impl/common-deployment-experiment-plan.md` (fixed, snapshot refreshed): section 11 has a current Status column, section 13 an update bullet, input 13 of section 16 is marked answered, section 22 is marked settled, section 53 names `aead_open_seal` too, section 130 records the O21 integration, and section 131 records the decisions and these fixes.
- `doc/impl/deployment-experiment.md` (fixed): the ideal-operations table has the selection, query class and bill, and loss term of every operation; the budgets paragraph records the cap decision; the O21 entries say integrated; a new last section states that the headlines are within the approved input 13 list.
- `doc/proverif-source-scope.md` (fixed): lines 64-70 carry an update note; the O21 cells say integrated.
- `doc/impl/common-deployment-experiment.md` (fixed): lines 2119, 2182, 2197 and 2212 say that `PqxdhDeploymentIdealLaterPool.onBase_view`'s guard list under-reports and that the theorem reaches all three standard axioms; the historical CE-3 trial table has a note with the current statement counts. The receipt `doc/impl/proof-receipts/lqf-upstream-B.json` still records the guard lists; it is a dated record and is not edited.
- `doc/impl/extract-composition.md` (fixed): the status line has a current lead sentence, which also records the receipt drift below and that the plan snapshot's section 8 coverage table describes the registration segment only.
- `doc/impl/proof-receipts/extract-composition-inc4.json` (not edited, documented): it records the pre-review hash `92a5471b…` of `PqxdhRegistrationJointKemKeyFirst.lean` (before the docstring-only fix `7f795e19`); the committed file hashes to `b6b38ca9…`, which the reviewed inventory pins. A receipt is a dated record, so the drift is documented in the guide instead of rewriting the receipt.
- `doc/impl/proof-receipts/common-deployment-experiment-o21.json` (fixed): an `integration` record states the integration at `c6ee2307`.
- Item 1 and record-lift guides (fixed): `doc/impl/registration-joint-accept-cut.md:30`, `doc/impl/registration-accept-kem-join.md:267`, `doc/impl/record-lift-facts.md:43` and `doc/impl/record-lift-world-facts.md:21` carry update notes. `doc/impl/record-lift-interface.md:74` (written by Codex) is superseded by the note in the analysis's new last section.
- Not fixed, by rule: the stale module documentation of the published Lean modules `PqxdhRecordLiftComposition`, `PqxdhRecordLiftCtxBills`, `PqxdhRecordLiftInterface` (including `Caps.derivations`), `PqxdhRecordLiftLater`, `PqxdhRecordLiftCtxHybrid`, `PqxdhRecordLiftWorld`, `PqxdhRegistrationJointKemIdealKeys` and `PqxdhRegistrationJointKemSecondEntry`. Published modules are frozen, and editing them would change their oleans and inventory rows; the update notes in the guides and in the analysis state the current status instead.
- Not fixed, out of scope of a documentation pass: the about 16,400 `/tmp` references in 377 committed files (most in dated receipts and records), the missing historical `LEAN_PATH` cited by `doc/impl/handover/pause-2026-10-05/README.md:260`, the 36 legacy modules without `require_line_count` pins in `check-inventory.sh` (a maintained check), and the guard-coverage and policy-gate gaps of the axiom scan (Lean or gate changes, which need the owner).
- Findings of the confirming review of `d95dd6dd` (all fixed in this file): the definition of ASSUME's 330-theorem set (basis section), the dated record of input 13's approval and the integration (the update paragraph at the top, the statuses, the analysis's new last section), the basis of `SourceFullCorrect` (obligation 2, assumption ledger), the scan's command forms (step 7, program widened), "only" instead of "exactly" for the walk gate, the four prerequisite groups of `check-proverif` (step 5), and input 13 not conditioning CE-R1 and CE-C3 (the paragraph on input 13).

## Coordination state when this file was written (2026-10-17)

- Agent jobs: no lease, Lean slot, ProVerif lock or integration lease was held, and disk was at level OK (249.7 GiB free).
- Codex: inactive since 2026-10-09. Claude owns the item 2, 3, 4, 5 and 7 lanes and CE-14 (owner decisions of 2026-10-08 and 2026-10-10).
- The branch `codex/completion-handoff-2026-10-11` (worktree `/tmp/beaconcrypt-completion-handoff`) is registered to Claude; it was integrated into central at `d95dd6dd` on 2026-10-17, and the O21 branch `codex/deployment-o21` at `c6ee2307` after it.
- The update of 2026-10-17 is on branch `codex/completion-fixes-2026-10-17` (worktree `/tmp/beaconcrypt-completion-fixes`, registered to Claude before creation), documentation only, not yet reviewed or integrated. Its Lean runs were two checks through `coord.sh lean` against the published `c6ee2307` olean set (the step 7 walk and the O21 guard comparison, both exit 0); it ran no `make verify`, full `lake build`, ProVerif, mutation testing or `nix-collect-garbage`.

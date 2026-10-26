# LQ-F upstream design v2: targets, CE-11b unit 11b-L, item 2 over the logged source and `ideal_compile_server`

Snapshot of the LQ-F upstream design v2, the binding design of the LQ-F upstream lane (units D, C, A and B), copied on 2026-10-10 from the scratch file `/tmp/bc-arc-scratch/common-experiment/lqf-up/design-v2.md` (SHA-256 `8d8aa59762f648098c18f48973a232e0dbeea07bec2f09e0191756a7640d1531`) by the review fix pass of LQ-F upstream unit A2, so that the citations "LQ-F design-v2, section ..." and those of its decisions (D...) and critique responses (F...) in the guides, the analysis and the proof receipts resolve in the repository. Apart from this paragraph the text is the scratch file byte for byte; relative names in it (`design.md`, `critique.md`, `probe/` and the unit directories) refer to that scratch directory. The first design `design.md`, which this one supersedes and partly carries over ("as design.md §x"), is snapshotted at `doc/impl/lqf-upstream-design.md`; the critique is not snapshotted. A later revision of the scratch file replaces this snapshot wholesale.

Status: design only, revision of `design.md` (same directory) after the adversarial critique `critique.md` (18 findings), written 2026-10-10 in scratch (`/tmp/bc-arc-scratch/common-experiment/lqf-up`, registered to claude as "LQ-F upstream design"). This file supersedes `design.md`; where it says "as design.md §x" the cited list is carried over unchanged. No worktree, branch or commit was touched. Basis: central `/tmp/beaconcrypt-authenticated-root-completion` at `ab9986ef` (U7 integrated), published LEAN_PATH `/tmp/bc-coord/leanpaths/ab9986efb4c323c9ca62be9774405e0a880cb747.leanpath`. Every probe of section 9 was run at `ab9986ef` through `coord.sh lean claude …` with the Lean 4.34.0 toolchain binary, `-j1 -M8000`, `timeout 180`, no `-o`, at most two at a time. Plan references: CE plan §22-§23, §27, §49 (Q1), §95-§96; CE-12 `design.md` §9 and `design-v2.md` §10-§11 (adopted, plan §96); LQ-F guide `doc/impl/later-quantum-lqf-spike.md` (open points 3, 5, 8); item 2 guide `doc/impl/extract-composition.md`.

## 0. Summary of the revision

1. Names and process follow the adopted CE-12 v2: U-L1's targets are `laterSlotGame`, `slotLossL`, `rootBillL`; U-L2 is `ideal_compile_server`. They are frozen on day 1 by a new small unit D (definitions plus unfolding lemmas), which lets B start before A's theorems exist (F3, F4).
2. CE-12 v2's log-erasure spike (its critique E6) is answered negative by inspection with cited evidence (section 2, D9): item 2's stage lemmas are stated per source14 query, and the logged program reads two values no source14 request returns. The lift is the route; CE-12 v2's "3-6 if the spike succeeds" branch is closed.
3. F1 is fixed and proved: `split_later` needs a new list-of-points deferral `defer_seeds_later`; both are proved in the scratch probe `probe/DeferL.lean` with no `sorry`. The post handler only has to commute with seed completions; it need not keep the invariant.
4. B gets a 0.5-day spike B0 with a stop rule, the missing later forms of U6's first-part reductions and key-match facts, `laterWith_split`, and a redone middle CE layer for `compileSnapImpl`. Its budget is 4.5-6.5 (F2).
5. C absorbs U-L4, now unblocked at `ab9986ef`, and the LQ-F designation-range refinement (F5, F15).
6. A's module order is repaired (F7), and the inheritance chain and S0b items are added (F6, F8).
7. The post-run HMAC argument now covers both cases, prefix keys and residual reads, with corrected citations (F11). The R1 caveat is sharpened (F12), and the T7 condition is rephrased with a wider closure check (F13).
8. Effort: the planning budget is 10.25-15.25 agent-days (ceiling about 18). The expected figure from measured CE-11b U6 throughput is about 6-9. Elapsed time is 7-10 days at 1.5 effective tracks, or 5.5-8 if LQ-F takes both Lean lanes once CE-12 P1 is integrated (section 6).
9. Owner-level items: none (section 11).

## 1. Resolution of every critique finding

| # | Finding | Resolution | Evidence | Where |
| --- | --- | --- | --- | --- |
| F1 | `split_later` cannot be built from `defer_later` | Accepted. New generic `defer_seeds_later` (copy of `PqxdhDeploymentIdealDefer.defer_seeds` with continuation `PqxdhDeploymentFinishErasure.laterTail` and blindness `laterTail_blind`), then `split_later` at `splitSeeds`, `InvX`, `initial_invX`, `fixed_invX`, `realPost_commutes_seed`. One of the critique's three proposed premises is not needed: the post handler need not keep `inv`, because `discard_erase_list` uses the invariant only inside the run and asks only `Blind` of the continuation. The seed-blindness of `xreveal` is `rfl`. | `probe/DeferL.lean`: `defer_seeds_later` and `split_later` proved, no `sorry`, log `deferl.log` (only the `represent_later` statement `sorry`) | §4.2 C1, C2 |
| F2 | B underestimated; missing first-part lemmas | Accepted. B0 spike with a stop rule. Added to B1: `laterWith_split` (now in D2), `game_markedL`, `keymatch_later` (later forms of `game_trace`, `ideal_keymatch`), `ideal_cutMarkedL`, `ideal_prefixMarkedL`, `slotGameAtL_cut`, `itemRest_deadL`, `resumeMarked_deadL`, `selected_of_activeL`. The middle CE layer (`step_mergeMid`, `compile_simulationMid` of `PqxdhDeploymentIdealPostSource`, 57 theorems) is redone for `compileSnapImpl` in B2's `…IdealLaterMid`. B is re-estimated at 0.5 + 1.5-2 + 2.5-4 = 4.5-6.5. R4 now says that F-B does not avoid the ghost cost. | Guard counts at `ab9986ef`: `IdealPool` 11, `IdealPoolSource` 27, `IdealCut` 47, `IdealKeymatch` 44, `IdealBranch` 17, `IdealActive` 11, `IdealPostSource` 57; U6 parts 72, 107, 94 (65+29), 101 (56+45) (plan §63-§85) | §4.5-§4.7, §6, §8 R4 |
| F3 | Names and E6 not aligned with CE-12 v2 | Accepted. Adopted `laterSlotGame`, `slotLossL`, `rootBillL`, `ideal_compile_server`. The E6 outcome is recorded as negative (D9). | `probe/Stmts2.lean` elaborates `later_slots_two` and `ideal_compile_server` under these names (stubs `sorry`); D9 citations | §2 D9, §4 |
| F4 | Serial critical path; Lean-slot contention | Accepted. All targets go into unit D (day 1). B0/B1 start on D's oleans, and A runs in the other lane. Lanes are planned at 1.5 effective LQ-F tracks while CE-12 P1/P2 hold the second Lean lane. | `coord.sh lease list`: CE-12 P1 holding a Lean slot at 2026-10-10 | §5, §6 |
| F5 | Stale basis | Accepted. Rebased to `ab9986ef`. `SkelL`, `Hmac`, `Stmts` re-run there (exit 0). All 425 earlier names and 119 new citations are present. C+ (U-L4) is merged into C. | logs `skel-ab99.log`, `hmac-ab99.log` (empty), `stmts-ab99.log` (only `sorry` warnings), `names4.log` | §4.2, §9 |
| F6 | Bills need the logged inheritance chain | Accepted. `scanL_inherit`, `commandsL_inherit`, `opaqueScanL_inherit`, `sourcePreOpaqueL_inherit`, `sharedStartL_inherit` (copies of `PqxdhRegistrationJointKemRootExpand.*_inherit`, file `…RootExpandCount.lean`) go into A2's `…ItemBills`. | names present (`names4.log`) | §4.4 |
| F7 | Module order breaks dependencies | Accepted. A2 order is Root (no `_two`), Factor, Once (stage T and every `_two`: `rootClientL_two`, `entryClientL_two`, `opaqueBranchL_uniform_two`), Hybrid, Keys, Bills. All definitions are in D, so no definition crosses the order. | — | §4.4 |
| F8 | S0a/S0b list incomplete | Accepted. `client_markedL` (the logged accept and the Server read as `lift_marked`-style cases beside `PqxdhRegistrationJointBeaconOpaqueFinish.client_marked`) and `accept_freeL` (`PqxdhRegistrationJointBeaconOpaqueFinishRouter.accept_free` for `LaterServerCommands.accept`, transported along `accept_fst`/`ordered_source` because query bounds are invariant under `map`) added to `…ItemFree`. | `client_marked` is stated per `RevealSchedule.Spec` query (source line 523) | §4.3 |
| F9 | `postNative_real` needs more than `realRegAt_base` | Accepted and proved for `realRegAt`: `realRegAt_hmac` (`handler_quiet` for the log, `snapshotAt … none = snap` definitionally) is proved in the probe. The ideal and split instances follow from `idealProg_real` and `PqxdhDeploymentIdealCut.slotCore_lift`. | `probe/DeferL.lean` `realRegAt_hmac`, no `sorry`; `postNative_ideal` statement in `probe/Stmts2.lean` | §4.1 D2, §4.2 C2 |
| F10 | `represent_later` ill-typed as sketched | Accepted. Stated with `realPost`, which is polymorphic in the backend. Added `xreveal_mapBackend` (`rfl`, proved) and `realPost_mapBackend`. | `probe/DeferL.lean`: `represent_later` statement elaborates, `xreveal_mapBackend` proved | §4.2 C1 |
| F11 | Post queries also land in prefix keys; D3 citation | Accepted. Section 5(3) covers both cases. D3 now cites `PqxdhDeploymentLaterServerCompile.terminal_quiet`, `post_quiet` and `laterKind (.inr ()) = none` (proved `rfl` in the probe). The post-budget remark cites `compile_server_reads` and `compile_server_no_kem`. | `probe/DeferL.lean` (the `laterKind` example) | §2 D3, §5 |
| F12 | R1 caveat undersold | Accepted as exposition. The sharpened caveat goes into the docstrings of T7-L, `later_slots_two` and `slotLossL` and into the analysis paragraph. No statement changes. One correction to the critique's framing: classical item 2 also uses R1 alone (no DH-keyed component, contamination scan), so the formal assumption set is identical. What changes is that in LQ-F no second-line DH argument remains. | `doc/impl/extract-composition.md` lines 72, 261, 453 (R1 is the sole source of independence) | §5 |
| F13 | T7 condition too strong | Accepted. Rephrased: "the reveal is computed by the candidate-free client from oracle answers". The closure check covers `sharedClientL`, `postSkelL`, `rootClientL`, `entryClientL` and `laterSlotGame`. | — | §5, §5.1 |
| F14 | Calibration double-counts | Accepted. Item 2 increments are 133, 207, 127 and 187, where 187 contains S8's 88 and T8b's 3. U6 ran 72, 107, 94 (65+29) and 101 (56+45). U5 ran 85 (11+27+47 at `ab9986ef`). A is budgeted at the upper half. | `extract-composition.md` lines 22, 203, 378, 575 | §6 |
| F15 | LQ-F designation range missing | Accepted. Module `PqxdhDeploymentLaterTargetRange` in C: `range_game_create_later` (from `range_game_create` through `game_classical_event` at the cache-invariant, ledger-only event "some designation is out of range"), `designated_create_later`, `kem_transfer_server_create_two_sided`. | `designated_create_later` statement elaborates (`probe/Stmts2.lean`) | §4.2 C4, §7 |
| F16 | U-L3 reveal constraint not discharged | Accepted. `envReveal` reads `native.owners`, `snap`, `created.seed`, `log`. The R1 cache is in `native.shared` (`scheduleLens`), and the hidden-slot material is in the backend and the World's seed table. `envReveal_blind` (`rfl`) and `revealOf_strip` (kernels) discharge it. | `probe/DeferL.lean` `envReveal_blind`, proved by `rfl` | §4.2 C2, §5 |
| F17 | Read cap looks vacuous | Accepted. The read cap enters no bill, as in `LaterServerBills.adversary_bound` (LQ-F guide open point 8): `weighted_bound` needs a cap per kind, the read's weight is 0, and `compile_server_reads` meets the cap with one. | — | §4.4 Bills |
| F18 | Hybrid naming exception; docs missing from effort | Accepted. The exception is dropped: `PqxdhDeploymentLaterServerItemHybrid` is under the registered `PqxdhDeployment*` prefix and is generic only in its client argument. Each unit's "review to integration" now includes the plain-English entry in `doc/formal-verification-analysis.md`, the guide section and the receipt. | registry: `PqxdhDeployment*` module prefix owned by claude | §4, §6 |

## 2. Design decisions (implementation-level, Claude's; no owner input needed)

- D1 (lift, not generalization), D2 (one new grouped request `AcceptL`), D6 (U5/U6 architecture with ghosts) and D7 (confidentiality only; no T5, A2 or T8 on `compileServer`; no DH-keyed component) are unchanged from design.md §2.
- D3 (post phase is continuation), corrected citation: in item 2's view, `compileServer`'s terminal reads, its Server read and its post part are ordinary requests of the program. They issue no raw accept (`PqxdhDeploymentLaterServerCompile.terminal_quiet`, `post_quiet`), and the Server read has no source kind (`laterKind (.inr ()) = none`, `rfl`). So the same per-request lemmas handle them, inside the continuation after the cut or inside the prefix when the cut is never reached (section 5).
- D4 (generic hybrid): the generic definitions `hybridOf` and `entryDkOf` are in D1. The theorems are in `PqxdhDeploymentLaterServerItemHybrid`, under the registered prefix and generic only in the client.
- D5 (fixed real post phase): `idealLaterGame` (IL_g) uses `realPost`. D2 proves `postNative_ideal`, and C proves `postNative_split`, the bridges to the `postNative` form that `join_later` takes, from `idealProg_real`, `slotCore_lift` and `realRegAt_hmac`.
- D8 (target freeze first, new): U-L1's and U-L2's definitions (`laterSlotGame`, `slotLossL`, `rootBillL`, `idealLaterGame`, `laterOf`) are a separate small publication unit D. `rootBillL` is the classical `PqxdhRegistrationJointKemRootCosts.rootBill` at the transported budget. The logged prechallenge bills coincide with the classical closed form (`LaterServerBills.pre_uniform`, `pre_base`, `pre_decapsulations` have the classical numbers), the Server read weighs 0, and post coins, HMAC and hash enter through `laterTransported`.
- D9 (E6 outcome: the log-erasure route does not exist, new). CE-12 v2 §10 step 3 asked whether the logged source is "the classical source plus a run-determined log", so that S7/T and `ideal_compile` lift by program equalities plus one post-phase HMAC hop. The answer is negative, by inspection, for D1's reason:
  - Item 2's classical results take `work : OracleComp (SourceSpec KemSK) X` with `SourceSpec = RevealSchedule.Spec` (for example `PqxdhRegistrationJointBeaconFinishOnce.opaqueBranch_slots_two`). `compileServer` is a program over `LaterServerSource.Spec = RevealSchedule.Spec + LaterRead`, and its `second` reads the Server read's answer.
  - That answer holds two values that no source14 request returns. The ephemeral scalars are dropped by the classical collector (`LaterServerSource.collectLogged_fst`). The Server seed sits in the Server's identity-pool slot, which no source14 read reaches: `PqxdhRegistrationJointLiveRead.entryClient .identity` reveals only `entry.2.2.beacon.identity.1`, an owner slot.
  - Forgetting the log gives source14 back only for source14 programs (`LaterServerSource.program_projection`).
  - The KEM transfer lifted by program equality only because the KEM hop's proofs "never look inside" the scanned program (`PqxdhDeploymentLaterServerKemHop` module docstring, used by `LaterServerOpaque.branch_opaque`). Item 2's proofs work per source14 query (`skelImpl_reads`, `groupedClient_bound`, `client_marked`, …), so no generic restatement exists to instantiate.
  - Recorded as the closed branch of CE-12 v2 §11's lane-A row.

## 3. What exists and what is missing (verified at `ab9986ef`)

- Present, as design.md §1: the LQ-F chain, CE-11b's ideal game running the logged handler (`realRegAt`), `laterWith`, `erase_later`, `erase_later_ctx`, `realPost`, `realPost_commutes`, `laterWith_real`, `defer_later`, `realPost_commutes_seed`, `join_later`, `join_later_public`, `postNative`, `envReveal`, `c4_ideal_later`.
- Present, new at `ab9986ef`: `PqxdhDeploymentIdealHandoff.ideal_view_slots`, `ideal_world` and `ideal_world_view_slots` (U7). U-L4 is unblocked.
- Present, relevant to F1: `PqxdhDeploymentIdealDefer.defer_seeds`, `discard_erase_list`, `PointedSeeds`, `splitSeeds`, `InvX`. The existing `defer_later` is the single-point form (`PointedReg seedLens`), not the tool for `split_later`.
- Missing: everything in section 4. The list-of-points later deferral and `split_later` are proved in scratch only.
- Name checks (`probe/Names4.lean`, log `names4.log`): the 425 names of design.md (with its four namespace corrections) and 119 new citations are all present. The 22 proposed module namespaces are all absent. No file of those names exists in any `/tmp/beaconcrypt-*` worktree or in scratch.

## 4. Increments (final)

Conventions for every unit. One publication unit per row of section 6, built on a `codex/deployment-lqf-*` branch (the claude-owned `codex/deployment-*` prefix; worktree `/tmp/beaconcrypt-deployment-lqf-*`, registered at creation) from freshly fetched central. Each module gets one Lean commit: root import, inventory row, check-inventory block, `inv recount` before `inv rehash`. Every theorem gets an exact `#guard_msgs` over `#print axioms` allowing only `propext`, `Classical.choice` and `Quot.sound`. Probabilistic statements go in `𝒟[…]`. Each unit gets the contamination scan (no DH-keyed component, no fixed-HKDF item) and the candidate-freedom closure check (section 5.1). Then come the semantic and hygiene review, the fix pass, the confirming review and integration. The documentation is the plain-English section in `doc/formal-verification-analysis.md`, the guide section (D and A in `doc/impl/later-quantum-lqf-spike.md`, closing open point 3; C and B in `doc/impl/common-deployment-experiment.md` under CE-11b-L) and the receipt `doc/impl/proof-receipts/…-lqf-<unit>.json`. New declarations carry an `L` suffix or live in their own namespace; consumers qualify.

### 4.1 Unit D: targets (`codex/deployment-lqf-targets`; day 1)

D1 `PqxdhDeploymentLaterServerItemTargets` (definitions, about 12-18 theorems). Definitions:
- `AcceptL`, `GSpecL`, `acceptStepL`, `skelImplL`, `groupedClientL` (as `probe/SkelL.lean`).
- `skelResumeL` (the logged rest of the opaque cut).
- `postSkelL`, `sharedStartL`, `sharedClientL`, `rootClientL`, `entryClientL`, `entryDL` (signatures as design.md §3.3-§3.7).
- The generic `hybridOf`, `entryDkOf`, and `entryDkL k := entryDkOf … (entryClientL …) k`.
- `laterSlotGame` (`slotGame` with `entryClientL`: `(simulateQ (slotImpl (tableService (n := n))) (entryClientL …)).run' (emptyAlloc, PqxdhRecordLiftLazyTable.initial)`).
- `slotLossL` (as design.md's `slotLossL`, with `entryDkL`).
- `rootBillL := PqxdhRegistrationJointKemRootCosts.rootBill` (D8).

Theorems: `acceptStepL_fst` (proved in `probe/SkelL.lean`), the unfolding lemmas `groupedClientL_inl`, `groupedClientL_accept`, `groupedClientL_read`, `skelImplL_inl`, `skelImplL_accept`, and `later_guess_term` (probe `Hmac.lean`).

D2 `PqxdhDeploymentIdealLaterGame` (about 8-14 theorems): `idealLaterGame` (IL_g with `realPost`, as elaborated in `probe/Stmts2.lean`), `laterOf` (the projection of `laterWith_real`), `ceDecideL`, `laterWith_split` (per constructed Server, the run of `gameWith`'s handler followed by `laterTail`), `realRegAt_hmac` (proved in the probe), the generic `postNative_real` (premise: the registration handler answers HMAC as the native handler on the base with snapshot and log kept), `postNative_ideal` (statement in the probe), `laterWith_postNative` (congruence in the post handler) and `idealLater_postNative` (IL_g equals its `postNative` form).

Review focus: the targets are the logged counterparts of `slotGame`, the right-hand side of `opaqueBranch_slots_two` (no classical name), `rootBill` and `idealGame`, and `slotLossL`'s first term at `laterTransported` is `(qAccept + qFinish + qHmac + qHmac₂)/2^256` (CE-12 v2 §10 step 2).

### 4.2 Unit C: 11b-L, U-L4 and the LQ-F range (`codex/deployment-lqf-c6`)

C1 `PqxdhDeploymentIdealLater` (generic, about 16-24): `defer_seeds_later` (proved in the probe), `represent_later` with `realPost` (statement in the probe), `realPost_mapBackend`, `xreveal_mapBackend` (proved), `represent_split_later`, `game_moveSeeds_later`, `laterWith_param`, `join_later_draw`, `join_later_param` (statements as design.md §6 and `probe/Stmts.lean`, re-elaborated at `ab9986ef`).

C2 `PqxdhDeploymentIdealLaterEnv` (instances, about 14-22): `erase_ideal_later` (`erase_later_ctx` at `idealPair` with `realPost`, `realPost_commutes`), `represent_ideal_later`, `seed_move_later`, `ideal_to_splitX_later`, `ideal_to_splitEager_later` (`split_kernel`), `split_later` (proved in the probe), `ideal_to_split_later`, `postNative_split`, `c6_split`, `c6_ideal`, `c6_ideal_public`, `c6_idealGame` (needs D2), and `envReveal_blind` (F16; `rfl`, proved).

C3 `PqxdhDeploymentIdealLaterSlots` (U-L4, about 8-15):
- `post_noinstall`: the post phase of `envGD` (coins, BLAKE2b, HMAC) installs no hidden kernel. Built from `PqxdhRecordLiftLaterWorlds.laterChains_split`, `post_effects` and `effects_post`.
- `later_slots`: on `laterRealChains env_g`, either `IdealSlots` of the final view or `Anomaly` of the run transcript. Built from `ideal_view_slots` and `laterReal_event`. The anomaly is bounded on `first`'s run by `PqxdhDeploymentIdealAnomalyGuesser.anomaly_le_pk` (CE-12 v2 §10).

C4 `PqxdhDeploymentLaterTargetRange` (F15, about 5-9):
- `range_game_create_later`: every designation on a reached LQ-F outcome has `session < qAccept` and `k < qCreate`. Proof: the event "some designation of the ledger transcript is out of range" reads only the ledger, so it is cache-invariant. `game_classical_event` moves its probability to the classical game, where it is 0 by `range_game_create`. Support form by `probEvent_eq_zero_iff`.
- `designated_create_later` (statement in the probe).
- `kem_transfer_server_create_two_sided`: as CE-9b's `kem_transfer_create_two_sided`, over `Fin qAccept × Fin qCreate`.

### 4.3 Unit A1: item 2 lift, S0a-S1c (`codex/deployment-lqf-item2`)

The source budget is the logged `certified`, as in design.md §3:
```lean
certified : ∀ kind, work.IsQueryBoundP (fun q => laterKind q = some kind) (budget kind)
```

`…ItemFree` (S0a, S0b; about 30-36):
- `opaqueBranchL_free`, `opaqueBranchL_freeRouter`, as design.md §3.2.
- Added (F8): `client_markedL`, the logged accept and the Server read as `lift_marked`-style cases.
- Added (F8): `accept_freeL`, which transports `accept_free` along `accept_fst`/`ordered_source`.

`…ItemShared` (S1b; about 28-35): `opaqueBranchL_shared`, `acceptStepL_split`, `groupedResumeL_split`, `opaqueBranchL_grouped`, as design.md §3.3.

`…ItemSplit` (S1c with the post-run HMAC term; about 30-38): `TableKindL`, `scanL_potential`, `implL_grows`, `client_boundL`, `commandsL_cut`, `opaqueScanL_fits`, `sourcePreOpaqueL_fits`, `sharedStartL_fits`, `skelImplL_reads`, `groupedClientL_bound`, `sharedClientL_direct`, `certified_tableL`, `shared_splitL`, `opaqueBranchL_split`, as design.md §3.4. `opaqueScanL_fits` covers the case where the whole program, post phase included, completes inside the prefix (section 5(3)).

### 4.4 Unit A2: item 2 lift, S2-S8 (same branch, second review cycle; module order fixed per F7)

1. `…ItemRoot` (S2 without `_two`; about 14-18): `skelImplL_hidden`, `groupedClientL_group`, `postSkelL_hidden`, `rootClientL_root`, `splitGameL_root`.
2. `…ItemFactor` (S3b; about 18-24): `acceptStepL_rel`, `skelImplL_rel`, `skelResumeL_factor`, `postSkelL_factor`, `rootClientL_entry`, `eager_entryDL`, `uniformGameL_entry`.
3. `…ItemOnce` (stage T and every `_two` form; about 20-28): `KemOnceL`, `top_stepL`, `pre_stepL`, `commandsL_once`, `opaqueScanL_once`, `sourcePreOpaqueL_once`, `postSkelL_two`, `sharedStartL_once`, `rootClientL_two`, `entryClientL_two`, `opaqueBranchL_uniform_two`.
4. `…ItemHybrid` (generic in the client; about 12-16): `hybridOf_hop`, `hybridOf_telescope`, `uniform_hybridOf`, `hybridOf_all`, `slotGameOf_all`.
5. `…ItemKeys` (about 10-14): T7-L `opaqueBranchL_idealKeys_two`, `opaqueBranchL_allIdeal_two`, `opaqueBranchL_slots_two`, `later_slots_two` (as elaborated in `probe/Stmts2.lean`; first term `(B.accept + B.finish + B.hmac + post.hmac)/2^256` by `later_guess_term`).
6. `…ItemBills` (about 27-35): the inheritance chain `scanL_inherit`, `commandsL_inherit`, `opaqueScanL_inherit`, `sourcePreOpaqueL_inherit`, `sharedStartL_inherit` (F6); `wSourceL`, `groupedClientL_cost`, `skelImplL_cost`, `postSkelL_cost` (via the logged `source_sum`), `sharedStartL_total`, `rootClientL_coins`, `laterSlot_bills`. `rootClientL_coins` and `laterSlot_bills` take a Server-read cap that enters no bill (F17).

Reuse lists are those of design.md §3.5-§3.9.

### 4.5 B0: spike (scratch, 0.5 day, against D's oleans)

Prove three things in scratch:
- (i) `stepAtC_ghost`: a generic lemma lifting any quiet unghosted `StepAtC` to the ghosted middle state. The log is kept (`handler_quiet`) and the snapshot moves by `snapshotAt`.
- (ii) The non-selected logged accept step. It appends the same entry on both views.
- (iii) `step_serverRead`, from `ItemInv`'s `PoolOwned` and `later_read`.

Stop rule: if (i) is one generic lemma and (ii)-(iii) close within the 0.5 day, B proceeds on the U6-reuse route at the budget below. Otherwise B1/B2 are re-estimated (+1-2) before any branch commit, and the plan records the new figure. This is an estimate change, not an owner item.

### 4.6 Unit B1: prefix and branch reductions (`codex/deployment-lqf-compile`)

- `PqxdhDeploymentIdealLaterParams` (about 12-18): `entryClientAtL`, `laterSlotGameAt`, `laterSlotGame_pool`, `draws_swapL`.
- `PqxdhDeploymentIdealLaterBranch` (about 30-45; F2):
  - `game_markedL`.
  - `keymatch_later`: `game_trace` and `ideal_keymatch` carried to `laterWith` as run-phase support facts, through `laterWith_split` and the post frame.
  - `ideal_cutMarkedL`, `ideal_prefixMarkedL`, `slotGameAtL_cut`, `itemRest_deadL`, `resumeMarked_deadL`, `CutRelIndexedL`, `ideal_compile_server_of_selected`, `selected_of_activeL`, `ideal_compile_server_of_active`.
- `PqxdhDeploymentIdealLaterCut` (about 35-50): `compile_scanServer`, `sourcePoolL`, `commonPrefixL`, `ideal_cutL`, `ideal_prefixL`, `item2_prefixL`, `cutStateL`, `CutRelL`, as design.md §5 L-B1.

### 4.7 Unit B2: middle run and assembly (same branch, second review cycle)

- `PqxdhDeploymentIdealLaterMid` (about 45-60): `MidL`, `sourceMidL`, `compiledMidL`. Also `step_mergeMidL` and `compile_simulationMidL`, which redo U6's middle CE layer for `compileSnapImpl` (F2).
- `PqxdhDeploymentIdealLaterSteps` (about 40-60): `step_realL` (via B0's `stepAtC_ghost`), the accept steps, `step_identity`, `step_serverRead`, `ItemInvL`, `keep_allL`, `item_simL`. U6's `step_challenge`, `step_read` and public-HMAC `StepAt` (which also serves post HMAC) are reused.
- `PqxdhDeploymentIdealLaterPost` (about 35-50): `itemPost_middleL`, `activeCE_middleL`, `server_continuationMid`, `decision_mergeL`, `GoodMidL`, `middleInvL`, `activeBranchL_of_middle`, `active_branchL`.
- `PqxdhDeploymentIdealLaterCompile` (about 1-3): `ideal_compile_server`, as elaborated in `probe/Stmts2.lean`:
```lean
𝒟[laterSlotGame … (LaterServerTransfer.decision … g) (compileServer … first second) runtime budget.create (selectedKem budget g) g.1.val 2] {true} =
  𝒟[(fun o => decide (LaterServerTransfer.happens event (laterOf o) = true ∧ LaterServerTransfer.designated … claim (laterOf o) = some g)) <$> (idealLaterGame … budget g ensureInit bounds mode first second).run runtime] {true}
```
  The premises are the read-backs and the run budget of `first`, for every `second`. There is no post budget: the post part issues no field read, and KEM reads stay at 0 (`compile_server_reads`, `compile_server_no_kem`).

The later form of U7's `ideal_world` (`ideal_compile_server` composed with `c6_idealGame`) is a composition with no new proof. It goes into P3's chain module, as U7 did for the classical chain.

## 5. The post-run HMAC term (revised)

What the post adversary knows is as design.md §4: every revealed Beacon secret, the Server seed and every generated ephemeral, hence both hidden entries' 128-byte DH coordinates `m`, but not the ML-KEM output `u`.

Why the existing term covers post queries, with coefficient one:

(1) G1 (`PqxdhExtractRomHiddenSuffix.hidden_suffix_bound`) holds for every client. The bad event fixes only the 32-byte suffix, so the bound is `Q/2^256` whatever the client knows about `m`.

(2) The T7 condition, rephrased (F13): the candidate `u` is passed only to hidden reads, and the reveal is computed by the candidate-free client from oracle answers. `opaqueBranchL_shared` writes the logged branch as G1's `sharedGame`, and `sharedClientL` has no candidate argument. The reveal may depend on `u` through hidden-read answers. For example, whether owner k's challenge finish succeeds decides whether its one-time scalar is captured in the snapshot. G1 allows this, because it excludes only a candidate argument, not a dependence on answers.

(3) The post queries are counted in both cases (F11):
- (a) The selected accept is reached and encapsulates. The post HMAC queries come after the cut, and `sharedClientL_direct` places them in G1's residual at kind `.inl 6`.
- (b) The selected accept is never reached, or rejects before encapsulation. `opaqueScan` then completes the whole program inside the prefix: run, terminal reads, Server read and post phase. The post HMAC queries become prefix cache keys (`keys`, through `opaqueScanL_fits`).
- G1 charges prefix keys and residual direct reads against one total `Q`. In both cases the single cap `laterTransported (.inl 6) = B.hmac + post.hmac` bounds them (`compile_server_certified`, probe `Hmac.lean`). The term is `(B.accept + B.finish + B.hmac + post.hmac)/2^256`, and the post-run share is `post.hmac/2^256`.

The PRF and key-schedule hops are as design.md §4: the reductions simulate post HMAC exactly, and only the bills grow.

R1 caveat, sharpened (F12), to go into the docstrings of `opaqueBranchL_idealKeys_two`, `later_slots_two` and `slotLossL` and into the analysis paragraph:
- In LQ-F the post adversary knows `m` exactly. Each hidden entry is the R1 table at `padFF32 ‖ m ‖ u`, with only the shared 32-byte `u` unknown.
- Their unpredictability given `m`, and their mutual independence, rest on R1 alone. Classically `m` also contains honest-honest DH values the adversary cannot compute. Item 2's proof never uses them (it imports no DH-keyed component), but a reader could take them as a second line of defence; in LQ-F there is none.
- The bound and its premises (R1, HMAC-PRF, Extract-on-`uniform32`, `SourceFullCorrect`, the logged `certified`) are exactly those of classical T7.

U-L3's reveal constraint (F16): `revealL`, the environment's `envReveal`, excludes the R1 cache and the hidden-slot material. It reads `native.owners`, `snap`, `created.seed` and `log`. The R1 slice's cache lives in `native.shared`, and the slot material in the backend and the World's seed table (`envReveal_blind`, `rfl`). Owners' kernels are not read (`revealOf_strip`). KEM reads are 0 on `compileServer` (`compile_server_no_kem`).

### 5.1 Candidate-freedom closure check

For `sharedClientL`, `postSkelL`, `rootClientL`, `entryClientL` and `laterSlotGame`: the transitive definition closure mentions no KEM candidate binder, and the only consumer of G1's secret is the hidden-read handler. This is the check the classical S2 performed, extended per F13.

## 6. Effort and schedule

Calibration (F14):
- Item 2's increments were 133, 207, 127 and 187 theorems (the 187 includes S8's 88 and T8b's 3); classical stages S1b 79, S1c 86, S2 42, S3b 88, S7 36, stage T 85.
- CE-11b U5 was 85 (11+27+47) and U6 was 374 (72, 107, 94 = 65+29, 101 = 56+45).
- U6 took 4.25-4.75 actual days including reviews (CE-12 effort critique, finding 3), about 80-88 theorems per day all-in.

Planning figures keep the critique's per-unit ranges, plus D and the range piece. "Review to integration" includes the analysis entry, the guide section and the receipt (F18).

| Unit | Content | Theorems | Build | Review to integration | Total |
| --- | --- | --- | --- | --- | --- |
| D | targets (D1, D2) | 20-32 | 0.25 | 0.25-0.5 | 0.5-0.75 |
| C | 11b-L, U-L4, range (C1-C4) | 45-70 | 1-1.5 | 1-1.25 | 2-2.75 |
| A1 | S0a-S1c | 90-115 | 0.75-1.25 | 0.75-1 | 1.5-2.25 |
| A2 | S2-S8 | 101-135 | 1-2 | 0.75-1 | 1.75-3 |
| B0 | spike | — | 0.5 | — | 0.5 |
| B1 | params, branch, cut | 77-113 | 1-1.5 | 0.5 | 1.5-2 |
| B2 | middle, steps, post, compile | 122-174 | 1.75-3 | 0.75-1 | 2.5-4 |
| Sum | | 455-639 | | | 10.25-15.25 |

- Ceiling: about 18. This adds R1 or R3 copies (+0.3-0.5) and the B0 stop-rule branch (+1-2). Fallback F-A (+3-5) is excluded.
- Expected figure: the theorem counts at U6's measured throughput give about 6-9. The budget is kept because B0 and the S1b/S3b copies' memory and elaboration costs are unmeasured.
- Against §49 Q1 (14.5-27 nominal) the budget is lower. Against CE-12 v2 §11's lane-A row (5-12, or 3-6 "if the spike succeeds") the spike branch is closed and the row should read "10.25-15.25 budget, 6-9 expected".

Lanes. CE-12 v2 allows at most two Lean checks in flight; CE-12 P1/P2 holds lane B.
- Lane A1: D, then B0, B1, B2. Critical path 5-7.25.
- Lane A2, sharing time with CE-12 lane B: C, then A1, then A2. 5.25-8 of work.
- B0 and B1 start against D's branch oleans (a LEAN_PATH prefix, as the LQ-F integration did) without waiting for D's integration, and A starts the same way. C starts on central at once and merges D after its integration for `c6_idealGame`.
- Elapsed: about 7-10 days at 1.5 effective tracks; about 5.5-8 if, after P1's integration, LQ-F takes both lanes and P2 runs in the gaps. The latter is recommended because CE-12-L waits on this lane and P2 gates no classical headline. This is a lane decision, not an owner item.
- Then P3 (CE-12-L) and the later `ideal_world` composition: 1-2.

## 7. CE-12-L headlines unblocked

| Headline | Needs | After |
| --- | --- | --- |
| CE-KT-L, transfer form | `kem_transfer_server_two_sided` (exists), `later_slots_two` (A2), `ideal_compile_server` (B2) | A2 + B2 |
| CE-KT-L, tight target domain `Fin qAccept × Fin qCreate` | + `kem_transfer_server_create_two_sided` (C4) | + C |
| CE-KT-L, world form | + `c6_idealGame` (C2) | A2 + B2 + C |
| CE-APP-L, CE-LOR-L | + `later_slots`, `post_noinstall` (C3), `later_record_lift`, `later_idealRecords_fresh`, `later_idealRecords_lor` (exist), `anomaly_le_pk` | A2 + B2 + C |
| Bills | `laterSlot_bills` (A2), `kem_transfer_server_bills`, `c4_ideal_later` (exist) | A2 |
| Symbolic corollaries | run-phase classical terms via `game_classical_event` | not blocked |

## 8. Risks and fallbacks

- R1 (elaboration under `-M8000`): S1b and S3b copies, not measured (critique, "not verified"). Mitigation: per-request lemmas stay separate, assemblies are split across modules, and the first build of `…ItemShared` and `…ItemFactor` is time-boxed and measured.
- R2 (a classical lemma is not per-request): becomes a proof copy (+0.5).
- R3 (stage T collapse): copy `top_step`/`pre_step` (+0.3).
- R4 (ghosts in the middle run): decided by B0's stop rule. Fallback F-B (state-form split at the end of the run, then `laterTail` congruence, +1-2) also needs the ghosts in the middle state, so it does not avoid the ghost cost (F2). It only shortens the post-phase part.
- R5 (identity reads and the Server read in the middle): through item 2's post-challenge router with `PoolOwned`; history differences are erased as U6 does (`prepKnown_erase`).
- R6 (read cap): the premise enters no bill (F17).
- R7 (names): CE-12 v2 names adopted. Everything else carries an `L` suffix or its own namespace; the 22 namespaces were checked absent.
- R8 (overclaim): confidentiality only; no T5, A2 or T8 on `compileServer`; the sharpened R1 caveat (section 5); post queries classical, no QPT or QROM.
- R9 (frozen target wrong, new): if A2 or B needs a different `slotLossL`, `rootBillL` or `laterSlotGame`, frozen definitions are never edited. Add a primed definition with an equality or inequality lemma in the consuming unit. Mitigation: D copies the classical forms verbatim, and D's review compares them with `opaqueBranch_slots_two`, `rootClient_coins` and `slotGame`.
- R10 (Lean-slot contention, F4): two Lean checks in flight overall; heavy builds are scheduled around CE-12 reviews.

## 9. Probes (scratch, central `ab9986ef`)

- `probe/DeferL.lean` (new; exit 0, log `deferl.log`). The only warning is the `sorry` of the statement check `represent_later`. Proved: `defer_seeds_later`, `split_later`, `xreveal_mapBackend`, `realRegAt_hmac`, `envReveal_blind` and the `laterKind` read example.
- `probe/Stmts2.lean` (new; exit 0, log `stmts2.log`, only `sorry` warnings). These elaborate: the stubs `laterSlotGame` and `slotLossL`, `later_slots_two`, `idealLaterGame` with `realPost`, `laterOf`, `postNative_ideal`, `ideal_compile_server` and `designated_create_later`.
- `probe/Names4.lean` (new; exit 0, log `names4.log`): 425 old names, 0 missing; 119 new citations, 0 missing; 22 proposed namespaces, 0 present.
- `probe/Names5.lean` (new; exit 0, log `names5.log`): 24 further citations, 21 present as written. The other three exist under the namespaces cited unqualified here: `PqxdhDeploymentIdealAnomalyGuesser.anomaly_le_pk`, `PqxdhRecordFactsLaterFresh.later_idealRecords_fresh` and `PqxdhRecordFactsLaterLor.later_idealRecords_lor`. The library lemma `probEvent_eq_zero_iff` is present.
- Re-runs at `ab9986ef`: `probe/SkelL.lean` (`skel-ab99.log`, empty), `probe/Hmac.lean` (`hmac-ab99.log`, empty), `probe/Stmts.lean` (`stmts-ab99.log`, only `sorry` warnings).

## 10. Assumptions and non-claims

There is no new assumption, contract or idealization. A uses route R1, the HMAC-SHA-512 PRF game, the Extract game on `uniform32`, `SourceFullCorrect` and the logged source budget. B and C use `Phase1ReadBack`, `Phase2ReadBack` and the run budget, and for bills `KemBound` and `initBound`. The KEM step upstream uses `FunctionalDecapsulation` and ML-KEM IND-CCA, as `kem_transfer_server` does. The range piece uses only existing classical facts through `game_classical_event`. Nothing here claims authentication in the later mode, a QPT or QROM adversary, persistence, codec internals or primitive implementations. The two §27 profile exceptions replace deviation D6 only when the headlines land (LQ-8, P3).

## 11. Owner-level items

None. Notes for the plan (no decision needed):
1. The E6 log-erasure spike is closed, negative (D9).
2. The lane-A estimate is revised: budget 10.25-15.25, expected 6-9, elapsed 7-10 at 1.5 tracks or 5.5-8 with both lanes after P1.
3. The sharpened R1 caveat (F12) changes no statement or premise; it will appear in the analysis when A2 lands.

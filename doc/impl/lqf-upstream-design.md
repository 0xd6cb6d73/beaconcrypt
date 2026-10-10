# LQ-F upstream design: item 2 over the logged source, `ideal_compile_later` and CE-11b unit 11b-L

Snapshot of the first LQ-F upstream design, copied on 2026-10-10 from the scratch file `/tmp/bc-arc-scratch/common-experiment/lqf-up/design.md` (SHA-256 `542035f6225368bc943a845a3d52fece87df6715dad27f2b7bc2d7b63026e179`) by the review fix pass of LQ-F upstream unit A2. It is superseded by LQ-F design-v2 (snapshot `doc/impl/lqf-upstream-design-v2.md`), which carries some of its lists and decisions over unchanged ("as design.md §x"); it is kept so that those references and the guides' citations of it (for example its section 3.10) resolve in the repository. Apart from this paragraph the text is the scratch file byte for byte; relative names in it refer to that scratch directory. A later revision of the scratch file replaces this snapshot wholesale.

Status: design only, written 2026-10-10 in scratch (`/tmp/bc-arc-scratch/common-experiment/lqf-up`, registered to claude as "LQ-F upstream design"). No worktree, branch or commit was touched. Basis: central `/tmp/beaconcrypt-authenticated-root-completion` at `66f425ef` (branch `codex/full-proof-composition`), published LEAN_PATH `/tmp/bc-coord/leanpaths/66f425ef9639bf5a47b3726c2eeefd2f754c70e1.leanpath`. Lean was run only on scratch probes in `probe/` (section 11), through `coord.sh lean claude …`, `lean -j1 -M8000`, `timeout 180`, no `-o`. Plan references: CE plan §19, §22, §23, §27, §47-§49 (Q1), §85-§93; CE-11b design v2 §10.1; CE-12 design §9 (`/tmp/bc-arc-scratch/common-experiment/ce12/design.md`); LQ-F guide `doc/impl/later-quantum-lqf-spike.md`; item 2 guide `doc/impl/extract-composition.md`.

## 0. Summary

1. Three upstream pieces are scheduled by §49 Q1 for the LQ-F headlines: (a) item 2's T7/S7/T over the logged source, starting at `PqxdhDeploymentLaterServerOpaque.opaqueBranch` and with the post-run HMAC term (U-L1 of the CE-12 design); (b) `ideal_compile_later` for `laterWith`/`compileServer` (U-L2); (c) unit 11b-L (U-L3). The CE-12 design adds a fourth small piece, the post-phase slot invariance U-L4, which this design schedules with (c) as an optional stage.
2. Facts found on central that shrink the work: CE-11b's ideal game already runs the LQ-F run-phase handler (`PqxdhDeploymentIdealSteps.realRegAt` is `PqxdhDeploymentLaterServerGame.handler` on the deployment state and the log, `XState` carries `snap` and `log`, the selected accept is built from `PqxdhDeploymentLaterServerNative.acceptLogged`); `PqxdhDeploymentFinishErasure.laterWith`, `erase_later`, `erase_later_ctx`, `realPost`, `realPost_commutes`, `laterWith_real`, `PqxdhDeploymentSeedSplit.defer_later`, `realPost_commutes_seed`, `PqxdhDeploymentEnvironmentJoin.join_later`, `join_later_public`, `postNative`, `envReveal` and `PqxdhDeploymentIdealFrame.c4_ideal_later` exist. Of the 11b-L list, `c4_ideal_later` and the generic `defer_later` are done; the `defer_later` instance (`split_later`) is not.
3. (a) is a lift, not a generalization: the classical item 2 modules are frozen and are stated for `SourceSpec`; the Server seed and the ephemeral scalars are not reachable by any source14 program, so no reduction to classical item 2 exists. The lift adds one request to item 2's grouped interface (`GSpecL = GSpec + AcceptL`, the logged accept); the Server read becomes the existing identity-pool reveal request, and the log lives in the client state. Every per-request lemma of item 2 (stated per query of `GSpec` or `PqxdhRegistrationJointRevealSchedule.Spec`) then applies verbatim to the classical requests, and each layer gets exactly one new case, the logged accept, whose projection `acceptStepL_fst` is proved in a scratch probe. Only branch-level assemblies are re-proved.
4. The post-run HMAC term is covered by the existing guessing term with coefficient one: at the transported LQ-F caps it is `(qAccept + qFinish + qHmac + qHmac₂)/2^256` (probe-checked evaluation of `laterTransported`), because the post adversary's HMAC queries are direct reads of G1's residual and G1's bound does not depend on what the client knows about the coordinates `m` (section 4). The PRF and Extract terms absorb post HMAC queries under other keys; no new term, assumption or contract.
5. Effort, calibrated on 100-200 guarded theorems per working session (one session = one agent-day; simulation-heavy stages at the lower end): (c) 1-1.5 (+0.5 for U-L4), (a) 3-5, (b) 3-4.5; total about 7-11 nominal agent-days (risk-adjusted ceiling about 14), against §49's 14.5-27. Order: (c) and (a)'s first unit in parallel, then (a)'s second unit, then (b).
6. Unblocking: (a)+(b) unblock CE-KT-L (transfer form); adding (c) gives CE-KT-L's world form; (a)+(b)+(c)+U-L4 unblock CE-APP-L and CE-LOR-L (the record-lift later forms `later_record_lift`, `later_idealRecords_fresh`, `later_idealRecords_lor` are on central). Bills of every LQ-F headline need (a)'s bills stage.

## 1. What exists and what is missing (verified)

The names cited in this design as existing were checked against the root environment of `66f425ef` by `probe/Names.lean`, `probe/Names2.lean` and `probe/Names3.lean` (a `run_cmd` that tests `Environment.contains` for each fully qualified name): 426 names, 422 found as first written; the other four were first looked up in a wrong namespace and are cited correctly here: `PqxdhRegistrationJointKemEntryFactor.factoredServices`, `PqxdhDeploymentIdealKernel.idealSplitEager`, `PqxdhRegistrationJointKemEncapsulation.forward_actual` and `PqxdhRegistrationJointKemRootExpand.valueRead?`. Names of unit U7 (`PqxdhDeploymentIdealHandoff`, `ideal_view_slots`) are not on central and are cited as U7's.

- LQ-F chain on central: logged source `PqxdhDeploymentLaterServerSource` (`Spec = RevealSchedule.Spec KemSK + LaterRead`, `Log`, `beforeLogged`, `collectLogged_fst`), logged commands `PqxdhDeploymentLaterServerCommands` (`impl` with `Local = owners × log`, `accept`, `accept_fst`, `ordered`, `ordered_fst`, `scan`, `tag`, `commands`, `commands_embed`), the cut `PqxdhDeploymentLaterServerCut` (`rawResume`, `opaqueResume`, `rawResume_opaque`, `scanned`), the opaque branch `PqxdhDeploymentLaterServerOpaque` (`OpaqueContext`, `sourcePreOpaque`, `opaquePost`, `opaqueBranch`, `pre_opaque`, `post_opaque`, `transfer`), budget `PqxdhDeploymentLaterServerReserve.laterKind`, bills `PqxdhDeploymentLaterServerBills.pre_uniform`, `pre_base`, `pre_decapsulations`, `adversary_bound`, compile `PqxdhDeploymentLaterServerCompile.compileServer`, `compile_server_source`, `server_continuation`, `server_step`, `server_good`, `server_run`, `accept_merge`, `terminal_quiet`, `post_quiet`, budget transport `PqxdhDeploymentLaterServerCompileBudget.laterTransported`, `compile_server_certified`, `compile_server_reads`, `compile_server_no_kem`, `compile_server_creates`, transfer `PqxdhDeploymentLaterServerTransfer.decision`, `kem_transfer_server`, `kem_transfer_server_bills`, two-sided `PqxdhDeploymentLaterKemTwoSided.kem_transfer_server_two_sided`, `hop_close`.
- Missing for (a): every stage of item 2 after T6 for the logged source (S0a, S0b, S1b, S1c, S2, S3b, S4b, S7, T, S8, T8b; T8 and S6 are not needed, section 3.10).
- Missing for (b): the later analogue of CE-11b's units U5 and U6 (prefix, middle run, decision) for `compileServer` and `laterWith`.
- Missing for (c): `represent_later`, `represent_split_later`, `erase_ideal_later`, `postNative_erased` (here `postNative_real` and its instances), `split_later` (the `defer_later` instance), `join_later_param` (with `laterWith_param` and a draw form of `join_later`), `c6_ideal`, `c6_ideal_public`. Present: `c4_ideal_later`, generic `defer_later`.

## 2. Design decisions (implementation-level, Claude's; no owner input needed)

- D1 (lift, not generalization). Item 2 is re-proved over the logged source in new modules, reusing every classical per-request lemma. The alternatives were rejected: editing the classical modules (frozen, protocol section 3); restating classical item 2 generically over a source extension (re-proves all ~650 theorems, +3-5 days, kept as fallback F-A); reducing LQ-F to classical item 2 (impossible: no source14 program reads the Server seed or the ephemeral scalars, LQ-F guide "What the spike tests").
- D2 (one new request). The logged grouped interface is `GSpecL KemSK Response := GSpec KemSK Response + AcceptL` with `AcceptL : OracleSpec Pqxdh.Bytes := fun _ => Option Nat × Option ScalarBytes`. The logged grouped client keeps `(owners, log)` as its state (as `LaterServerCommands.Local` does), sends the raw accept as `.inr raw` and appends the returned entry, sends every other source14 request through the classical `groupedClient` lifted to `.inl`, and answers the Server read by the existing pool request `groupedPoolLift (.inl (.inr (.reveal identityIndex)))` (exactly the request `LaterServerCommands.impl` issues) paired with the log. The logged skeleton `skelImplL` is `skelImpl` on `.inl` and the logged accept step `acceptStepL` on `.inr`. Probe `SkelL.lean` elaborates all four definitions and proves `acceptStepL_fst` with no `sorry` (section 11).
- D3 (post phase is continuation). In (a) the post phase is not special: `compileServer`'s terminal reads, Server read and post part are requests of the program after the cut (all raw accepts are in the run part, `PqxdhDeploymentLaterCompile.continuation_no_accept`), so they are handled by the same per-request lemmas inside the skeleton's continuation.
- D4 (generic S7 hybrid). The indexed lazy-table hybrid of `PqxdhRegistrationJointKemSecondEntry` is stated for the closed `entryClient`; the lift states it once for any client `OracleComp (EntrySpec Output) Bool` with a value-read bound and instantiates it for `entryClientL` (classical instances stay as they are).
- D5 (fixed real post phase in 11b-L). Every representation of the ideal registration answers HMAC as `realRegAt` (`PqxdhDeploymentIdealSteps.idealProg_real`), so its `postNative` is `PqxdhDeploymentFinishErasure.realPost` (`postNative_real`, from `PqxdhDeploymentLater.post_embed` and `PqxdhDeploymentIdealCut.realRegAt_base`). The later chain then runs with one fixed post handler, the shape `erase_later_ctx` and `defer_later` already take, and `realPost_commutes` and `realPost_commutes_seed` discharge their premises.
- D6 (U5/U6 architecture kept for (b)). `ideal_compile_later` follows `ideal_compile`: common prefix, one middle run with two views (item 2's projection and CE's merge image), decision on the merge image. The middle state gains the ghosts (`MidL = Mid + snap + log`), because the LQ-F reveal reads them; U5's `idealRun_unghost` route (ghosts never read) no longer applies after the run.
- D7 (scope). LQ-F claims confidentiality only. T5, A2 and T8 are never cited on `compileServer` (LQ guide rule; `compileServer` reveals the Server identity). Key-first S6 for the logged source is not built (no CE-12-L consumer). No component keyed by DH secrecy is imported (LQ rule; the contamination scan of item 2 is rerun on every new module).

## 3. (a) Item 2 over the logged source (U-L1)

Notation: `L…` names are new; `…` abbreviates `setup codec checks ensureInit supplied decision work runtime count selected index` with `work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X`; the source budget is the logged form of T5's `certified`:

```lean
(budget : PqxdhRegistrationJointRevealCosts.SourceKind → ℕ)
(certified : ∀ kind, work.IsQueryBoundP
  (fun q => PqxdhDeploymentLaterServerReserve.laterKind (KemSK := KemSK) q = some kind) (budget kind))
```

The Server read has kind `none`; it makes no table read, no hidden read, no creation and no decapsulation, so no stage needs a cap on it except the bills (L-A9, as `LaterServerBills.adversary_bound`, met by `compile_server_reads`).

### 3.1 L-A1 infrastructure (`PqxdhDeploymentLaterServerItemSkeleton`, about 15 theorems)

```lean
abbrev AcceptL : OracleSpec Pqxdh.Bytes := fun _ => Option Nat × Option PqxdhJointGapDh.ScalarBytes
abbrev GSpecL (KemSK Response : Type) := PqxdhRegistrationJointKemPostSkeleton.GSpec KemSK Response + AcceptL
noncomputable def acceptStepL … (raw) : SClient KemSK V (Option Nat × Option ScalarBytes)   -- `acceptStep` with LaterServerCommands.ordered
noncomputable def skelImplL … (services) : QueryImpl (GSpecL KemSK Response) (SClient KemSK V)
noncomputable def groupedClientL setup codec selected challenge identityIndex :
  QueryImpl (PqxdhDeploymentLaterServerSource.Spec KemSK) (StateT (List EncodedEntry × Log) (OracleComp (GSpecL KemSK Response)))
theorem acceptStepL_fst … (state) :
  (fun r => (r.1.1, r.2)) <$> (acceptStepL … raw).run state = (PqxdhRegistrationJointKemPostSkeleton.acceptStep … raw).run state  -- proved in probe
def TableKindL : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain → Prop   -- `TableKind` on `.inl`, False on the read
theorem scanL_potential …   -- `PqxdhRegistrationJointKemRomSplit.scan_potential` for `LaterServerCommands.scan`
theorem scanL_inherit …     -- `PqxdhRegistrationJointKemRootExpand.scan_inherit` for `LaterServerCommands.scan`
theorem groupedClientL_inl / groupedClientL_accept / groupedClientL_read   -- unfolding lemmas
```

Route: definitions as in `probe/SkelL.lean`; `acceptStepL_fst` from `LaterServerCommands.ordered_fst` and `PqxdhRegistrationJointKemSourceSuffix.ordered_source` (done). `scan_potential` and `scan_inherit` are generic in the handler but stated for the classical `AcceptCut.scan`; the logged copies are proof copies (the logged scan forwards the read unchanged).

### 3.2 L-A2 S0a and S0b (`PqxdhDeploymentLaterServerItemFree`, about 30 theorems)

```lean
theorem opaqueBranchL_free … (real : Bool) :
  PqxdhDeploymentLaterServerOpaque.opaqueBranch … real = freeBranchL … real
theorem opaqueBranchL_freeRouter … (real : Bool) :
  PqxdhDeploymentLaterServerOpaque.opaqueBranch … real = freeRouterBranchL … real
```

Reused unchanged: `PqxdhRegistrationJointKemObserverFree.run_erase`, `run_eraseOption`, `router_neverRead`, `identity_neverRead`, `post_neverRead`, `impl_neverRead` (every `.inl` request of `LaterServerCommands.impl` runs `KemEncapsulation.impl` on `RevealSchedule.client`), `resume_neverRead` (the resumption is unchanged), `decision_erase`; `PqxdhRegistrationJointBeaconOpaqueFinish.layered`, `mark_run`, `router_moves`, `owner_marked`, `client_marked`; `PqxdhRegistrationJointBeaconOpaqueFinishRouter.markedResume_unmarked`, `finish_unmarked`, `accept_free`. New: `acceptL_neverRead` (the logged accept never reads observers: `accept_neverRead`'s proof on `LaterServerCommands.prepare`), the read case (a pool request, no native state), `implL_neverRead`, the logged rest of `LaterServerCut.opaqueResume` (owners and log), `client_freeL` (neither the logged accept nor the read sends the selected decapsulation), and the two branch equalities.

### 3.3 L-A3 S1b (`PqxdhDeploymentLaterServerItemShared`, about 28 theorems)

```lean
noncomputable def sharedStartL … : ProbComp (HmacOracle.QueryCache × (MlKem768PublicKey × KemSK) × LaterServerOpaque.OpaqueContext Reader KemSK A X count × MlKem768Ciphertext)
noncomputable def postSkelL setup codec checks decision count selected (services : Services V Response) chosen challenge
    (context : PqxdhDeploymentLaterServerOpaque.OpaqueContext Reader KemSK A X count) : OracleComp (SkelSpec V) Bool
noncomputable def sharedClientL setup codec checks decision count selected := fun context =>
  simulateQ (PqxdhRegistrationJointKemPostSkeleton.compileHidden setup.hmac) (postSkelL … (nativeServices setup codec checks) …)
theorem opaqueBranchL_shared … :
  PqxdhDeploymentLaterServerOpaque.opaqueBranch … false =
    PqxdhExtractRomHiddenSuffix.sharedGame (sharedStartL …) (sharedClientL setup codec checks decision count selected)
```

Reused unchanged: `PqxdhRegistrationJointKemPostSkeleton.groupedImpl_split` for every `.inl` request, `resumeImpl_split`, `push_stateless`, `push_option`, `split_run`, `fwd`, `fwdOption`, `shared_compile`, `evalLayer`, `groupedFinish`, `groupedPoolLift`, and `PqxdhRegistrationJointKemEncapsulation.forward_actual`. New: `acceptStepL_split` (the logged accept is the skeleton step followed by `opRoot`: the classical accept proof with `ordered` in place of `clientPrefix`; the extra output is the entry), `groupedResumeL_split` (the whole logged resumed client), `opaqueBranchL_grouped`, `skelResumeL`, `postSkelL`, `sharedStartL`, `sharedClientL`. `postSkelL` is `postSkel` with `skelImplL`, `groupedClientL` and the logged rest of the opaque cut (log at the cut extended by the selected accept's `some ephemeral.secret`, `LaterServerCut.rawResume_opaque`). This equality is also the Lean form of the T7 condition: the candidate is G1's secret, passed only to hidden reads; the client that computes the reveal has no candidate argument (section 4).

### 3.4 L-A4 S1c with the post-run HMAC term (`PqxdhDeploymentLaterServerItemSplit`, about 28 theorems)

```lean
theorem opaqueBranchL_split … (budget) (certified) :
  (PqxdhDeploymentLaterServerOpaque.opaqueBranch … false).boolDistAdvantage
      (PqxdhExtractRomHiddenSuffix.splitGame (sharedStartL …) (sharedClientL …)) ≤
    ((budget (.inl 3) + budget (.inl 5) + budget (.inl 6) : ℕ) : ℝ) / 2 ^ 256
theorem later_guess_term (bounds : FreshBounds) (B : Budget) (post : PqxdhDeploymentLater.PostBudget) :
  laterTransported bounds B post (.inl 3) + laterTransported bounds B post (.inl 5) +
    laterTransported bounds B post (.inl 6) = B.accept + B.finish + (B.hmac + post.hmac)   -- probe-checked by `simp`
```

Reused unchanged: `PqxdhExtractRomHiddenSuffix.hidden_suffix_bound` (G1, generic in the start and the client), `PqxdhRegistrationJointKemRomSplit.potential_run`, `growsN_*` and `growsN_acceptTail`, `impl_grows` and `client_bound` on `.inl`, `skelImpl_reads` and `groupedClient_bound` on `.inl`, `resumeImpl_reads`, `fwd_reads`/`fwdOption_reads` (forwarding through the lower layers is unchanged). New: `implL_grows` (logged accept: one key, its root read; read: none), `client_boundL`, `commandsL_cut`, `opaqueScanL_fits`, `sourcePreOpaqueL_fits`, `sharedStartL_fits`, `skelImplL_reads`, `groupedClientL_bound`, `sharedClientL_direct`, `certified_tableL`, `shared_splitL`, `opaqueBranchL_split`, `later_guess_term`.

### 3.5 L-A5 S2 (`PqxdhDeploymentLaterServerItemRoot`, about 16 theorems)

```lean
noncomputable def rootClientL … : OracleComp PqxdhCorrelatedExpand.RootSpec Bool :=
  PqxdhRegistrationJointKemRootExpand.internalize (sharedStartL …) (fun c => postSkelL … (nativeServices …) …)
theorem splitGameL_root … : splitGame (sharedStartL …) (sharedClientL …) = randomGame (simulateQ (compile setup.hmac) (rootClientL …))
theorem opaqueBranchL_uniform_two … (budget) (certified) :
  (opaqueBranch … false).boolDistAdvantage (PqxdhCorrelatedExpandHybrid.uniformGame (rootClientL …)) ≤
    ((budget (.inl 3) + budget (.inl 5) + budget (.inl 6) : ℕ) : ℝ) / 2 ^ 256 +
      ∑ slot ∈ Finset.range 2, (hmacPrfRealGame setup.hmac (indexedReduction setup.hmac (rootClientL …) slot)).boolDistAdvantage
        (hmacPrfRandomGame (indexedReduction setup.hmac (rootClientL …) slot))
```

Reused unchanged: `PqxdhRegistrationJointKemRootExpand.internalize`, `publicLocal`, `splitGame_local` (generic in start and post), `PqxdhCorrelatedExpandHybrid.expanded_uniform_bound`, `skelImpl_hidden` and `groupedClient_group` on `.inl`, `resumeImpl_hidden`. New: the logged accept makes no hidden read, `skelImplL_hidden`, `groupedClientL_group`, `postSkelL_hidden`, `rootClientL_root`. The count 2 comes from L-A6.

### 3.6 L-A6 stage T (`PqxdhDeploymentLaterServerItemOnce`, about 20 theorems)

```lean
def KemOnceL (selected : Nat) {count : Nat} : LaterServerOpaque.OpaqueContext Reader KemSK A X count → Prop
theorem postSkelL_two … (once : KemOnceL selected.val context) :
  (postSkelL … services chosen challenge context).IsQueryBoundP (fun q => PqxdhRegistrationJointKemRootExpand.valueRead? q = true) 2
theorem sharedStartL_once … : ∀ start ∈ support (sharedStartL …), KemOnceL selected.val start.2.2.1
theorem rootClientL_two … : (rootClientL …).IsQueryBoundP PqxdhCorrelatedExpandHybrid.IsRoot 2
theorem entryClientL_two … : (entryClientL …).IsQueryBoundP (IsValue (D := PqxdhCorrelatedExtractFamily.Message) (R := Output)) 2
```

Reused unchanged: `PqxdhRegistrationJointBeaconFinishOnce.composeOpt`, `option_potential`, `option_invariant`, `ownerCount`, `pending`, `client_count`, `groupedClient_count`, `skelImpl_marked`, and `top_step`/`pre_step` for `.inl` requests through a projection lemma (the logged collapse `topImplL`/`preTopL` on a non-accept `.inl` request is the classical collapse with the log kept, and the potential does not read the log). New: the logged accept and the read keep the potential (no creation, no finish), `top_stepL`, `pre_stepL`, `commandsL_once`, `opaqueScanL_once`, `sourcePreOpaqueL_once`, the four statements above.

### 3.7 L-A7 S3b (`PqxdhDeploymentLaterServerItemFactor`, about 18 theorems)

```lean
theorem postSkelL_factor … :
  postSkelL … (nativeServices setup codec checks) chosen challenge context =
    simulateQ (relabelS (PqxdhServerAuthKeySchedule.fromRoot setup.source))
      (postSkelL … (PqxdhRegistrationJointKemEntryFactor.factoredServices setup codec checks) chosen challenge context)
noncomputable def entryClientL … := internalizeV (sharedStartL …) (fun c => postSkelL … (factoredServices …) …)
noncomputable def entryDL … : PqxdhServerAuthKeySchedule.Distinguisher
theorem uniformGameL_entry … :
  𝒟[PqxdhCorrelatedExpandHybrid.uniformGame (rootClientL …)] = 𝒟[PqxdhServerAuthKeySchedule.rootHybrid setup.source (entryDL …)]
```

Reused unchanged: `PqxdhRegistrationJointKemEntryFactor.skelImpl_rel` on `.inl`, `resume_rel`, `challenge_rel`, `map_run_inv`, `internalizeV`, `internalize_relabel`, `firstTable`, `firstTable_relabel`, `eagerImpl_eq`, `PqxdhRootFirstEntry.uniformGame_first`. New: `acceptStepL_rel` (the accept's tail is the classical one; the entry is related to itself), `skelImplL_rel`, `skelResumeL_factor`, `postSkelL_factor`, `rootClientL_entry`, `eager_entryDL`, `uniformGameL_entry`.

### 3.8 L-A8 S7, T7 and the slot form (`PqxdhDeploymentLaterServerItemHybrid` generic, about 14; `PqxdhDeploymentLaterServerItemKeys`, about 12)

```lean
-- generic in the client (D4)
noncomputable def hybridOf (source) (client : OracleComp (EntrySpec Output) Bool) (k : ℕ) : ProbComp Bool
noncomputable def entryDkOf (source) (client) (k : ℕ) : PqxdhServerAuthKeySchedule.Distinguisher
theorem hybridOf_telescope (source hmac correct) (client) (n) (bounded : client.IsQueryBoundP IsValue n) (first : …) : …
theorem slotGameOf_all (client) (n) (bounded : client.IsQueryBoundP IsValue n) :
  (simulateQ (slotImpl (tableService (n := n))) client).run' (emptyAlloc, PqxdhRecordLiftLazyTable.initial) =
    (simulateQ lazyImpl client).run' ∅
-- the logged instance (headline U-L1)
noncomputable def slotGameL … (n : ℕ) : ProbComp Bool := (simulateQ (slotImpl (tableService (n := n))) (entryClientL …)).run' (emptyAlloc, PqxdhRecordLiftLazyTable.initial)
noncomputable def slotLossL … (budget) : ℝ :=
  ((budget (.inl 3) + budget (.inl 5) + budget (.inl 6) : ℕ) : ℝ) / 2 ^ 256 +
    ∑ slot ∈ Finset.range 2, (hmacPrfRealGame setup.hmac (indexedReduction setup.hmac (rootClientL …) slot)).boolDistAdvantage
      (hmacPrfRandomGame (indexedReduction setup.hmac (rootClientL …) slot)) +
    ∑ k ∈ Finset.range 2, PqxdhRegistrationJointKemSecondEntry.keyScheduleBound setup.source setup.hmac (entryDkL … k)
theorem opaqueBranchL_idealKeys_two … (budget) (certified) (correct : SourceFullCorrect setup.source setup.hmac) : …  -- T7-L
theorem opaqueBranchL_slots_two … (budget) (certified) (correct : SourceFullCorrect setup.source setup.hmac) :
  (PqxdhDeploymentLaterServerOpaque.opaqueBranch … false).boolDistAdvantage (slotGameL … 2) ≤ slotLossL … budget
theorem later_slots_two (setup codec route checks) (correct) (ensureInit bounds mode first second) (B : Budget)
    (respects : B.Respects first) (post : PostBudget) (postRespects : ∀ o r, post.Respects (second o r)) (event claim g runtime) :
  (LaterServerOpaque.opaqueBranch setup codec checks ensureInit none (LaterServerTransfer.decision … g)
      (compileServer setup codec route bounds mode first second) runtime B.create (selectedKem B g) g.1.val false).boolDistAdvantage
    (slotGameL setup codec checks ensureInit none (LaterServerTransfer.decision … g) (compileServer …) runtime B.create
      (selectedKem B g) g.1.val 2) ≤ slotLossL … (laterTransported bounds B post)
```

`later_slots_two` instantiates `certified` with `compile_server_certified`; with `later_guess_term` its first term is `(B.accept + B.finish + B.hmac + post.hmac)/2^256`. Reused unchanged: `PqxdhRegistrationJointKemSecondEntry.keyScheduleBound`, `indexed_eager_output`, `indexed_lazy`, `slot_lazy`, `slotImpl`, `tableService`, `PqxdhKeyScheduleFromRoot.fromRoot_bound`. The generic hybrid is the proof of `hybrid_hop`, `hybrid_telescope`, `uniform_hybrid`, `hybrid_all`, `slotGame_all` with the closed client abstracted; its only client-specific inputs are the value-read bound and `uniformGameL_entry`.

### 3.9 L-A9 bills (`PqxdhDeploymentLaterServerItemBills`, about 22 theorems)

```lean
def wSourceL (caps) : Option SourceKind → ℕ          -- wSource on `some`, the read 0
theorem groupedClientL_cost / skelImplL_cost / postSkelL_cost / sharedStartL_total
noncomputable def rootBillL (caps qInit supplied count budget) : ℕ   -- prefixBillL + postBillL
theorem rootClientL_coins … (reads : work.IsQueryBoundP (fun q => laterKind q = none) r) : (rootClientL …).IsQueryBoundP IsCoin (rootBillL …)
theorem laterSlot_bills … : (∀ slot ∈ Finset.range 2, PrfBills setup.hmac (rootClientL …) slot (rootBillL …)) ∧
  ∀ k ∈ Finset.range 2, EntryComponentBills setup.source setup.hmac (entryDkL … k) (rootBillL … + 216)
```

Reused unchanged: `PqxdhRegistrationJointKemRootCosts.WBound`, `wBound_simulate`, `wBound_run`, `wBound_option`, `wBound_kinds`, `skelImpl_cost` and `groupedClient_cost` on `.inl`, `ServiceBills` with `nativeServices_bills`/`factoredServices_bills`, `resume_cost`, `PqxdhRegistrationJointKemKeyTransfer.PrfBills`, `prf_bills`, `PqxdhServerAuthEntryFactor.entry_component_bills`. The prefix bill goes through `LaterServerOpaque.pre_opaque` and the logged raw-ordinal prechallenge bills `LaterServerBills.pre_uniform`, `pre_base`, `pre_decapsulations` instead of `KemRawChallenge.preRaw_source`. The post budget enters through `laterTransported` (64 per post HMAC and hash, one per post coin).

### 3.10 Not built for LQ-F

T8 (`authenticated_*`): T5 must not be cited on `compileServer`; LQ-F claims no authentication. S6 key-first: no CE-12-L consumer (CE-11b's own key-first forms are classical). The `1 + qFinish` forms (only the `_two` forms are needed).

## 4. The post-run HMAC term

What the post adversary knows. `A₂` receives `(revealOf owners snap, (some serverSeed, log))`: every Beacon identity seed, prekey scalar and successful one-time scalar, the Server identity seed and every generated Server ephemeral scalar. From these and the public transcript it computes every DH output, so it knows the 128-byte coordinates `m` of both hidden entries (the selected accept's and owner k's challenge finish), which in the classical run it may not know. It does not know the ML-KEM shared secret `u`: no ML-KEM secret is revealed, and after T4, the KEM hop and T6 (`kem_transfer_server`, `kem_transfer_server_two_sided`) `u` is the challenger's uniform candidate. Each hidden entry is the R1 table at `padFF32 ‖ m ‖ u`.

What its HMAC queries can do. A post query on the zero-key 192-byte slice is a direct read of the one table. It reaches a hidden entry only if its input is `padFF32 ‖ m' ‖ u` for some `m'`, that is only if its 32-byte suffix is `u`. This is G1's bad event. A query under any other key is real HMAC and touches no table entry.

Why the existing term covers it, with coefficient one. (1) `hidden_suffix_bound` holds for every client `C → OracleComp HiddenSpec Bool`: the bad event is a function of the direct-read log of the split run, the split run draws no secret, every string has the hidden shape for at most one 32-byte secret, and the union bound runs over at most `Q` strings, so the bound is `Q/2^256` whatever the client knows about `m` (the hidden shape fixes only the suffix). Knowing `m` lets `A₂` aim at the right coordinates, but each aimed query still guesses `u` with probability `2^-256`. (2) The T7 condition (no reveal entry is a function of `u`) is discharged structurally by L-A3: `opaqueBranchL_shared` writes the logged branch as G1's `sharedGame` with `u` drawn after `sharedStartL` and passed only to hidden reads, and `sharedClientL`, which computes the reveal from the client log (scalars logged by `.generate`, the selected one fixed before the encapsulation by `LaterServerCut.rawResume_opaque`) and from the identity pool, has no candidate argument. (3) The post queries are counted: they are `.hmac` requests of `compileServer` after the cut, so `sharedClientL_direct` puts them in G1's residual through `certified` at kind `.inl 6`, and `laterTransported (.inl 6) = B.hmac + post.hmac`. Hence the term is `(B.accept + B.finish + B.hmac + post.hmac)/2^256` (`later_guess_term`, probe `Hmac.lean`); the post-run share is `post.hmac/2^256`.

The PRF and key-schedule hops. After S1c each hidden PRK is a uniform block of the coordinate-keyed table, read only by its Expand. A post HMAC query keyed by that PRK is real HMAC in both H1 and H2; the reduction `indexedReduction setup.hmac (rootClientL …) slot` runs `rootClientL`, including the post phase and the reveal, and answers such queries with the real function, so its simulation is exact in both worlds and the PRF advantage already pays for any guess of the key. The same holds for G2's Extract-on-`uniform32` and PRF reductions on `entryDL` and `entryDkL k`. Only the bills grow (L-A9). BLAKE2b post queries are not item 2 terms (they enter `c4_ideal_later`'s `+ post.hash` and the record-lift CTX terms). No explicit extra bound is needed; if `sharedClientL_direct` could not count the post reads in the same residual, the fallback is a second application of G1 to the post phase with its own budget, which costs the same `post.hmac/2^256`.

## 5. (b) `ideal_compile_later` (U-L2)

Target statement (elaborated with a stub of `slotGameL` in `probe/Stmts.lean`):

```lean
noncomputable def idealLaterGame (budget) (g) (ensureInit) (bounds) (mode) (first) (second) := fun runtime => do
  let p ← PqxdhDeploymentIdealParams.drawParams setup budget.create
  (laterWith setup codec route PqxdhDeploymentIdealSteps.idealInit (idealReg setup codec route checks (Target.ofCE budget g) p)
    (fun created => postNative setup codec route (idealReg setup codec route checks (Target.ofCE budget g) p created))
    ensureInit 0 bounds mode first second).run runtime
theorem ideal_compile_later (phase1 : Phase1ReadBack codec) (phase2 : Phase2ReadBack codec) (ensureInit) (bounds) (mode)
    (first : OracleComp (ModeSpec mode) X) (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out)
    (budget : Budget) (respects : budget.Respects first) (event claim) (g) (runtime) :
  𝒟[slotGameL setup codec checks ensureInit none
      (PqxdhDeploymentLaterServerTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
      (PqxdhDeploymentLaterServerCompile.compileServer setup codec route bounds mode first second) runtime budget.create
      (PqxdhDeploymentKemTransfer.selectedKem budget g) g.1.val 2] {true} =
    𝒟[(fun o => decide ((observeLater o.1).any event = true ∧
        (observeLater o.1).bind (PqxdhDeploymentKemTransfer.target setup.source.crypto codec setup.serverKeyId budget claim) = some g))
      <$> (idealLaterGame setup codec route checks budget g ensureInit bounds mode first second).run runtime] {true}
```

with `observeLater o := o.map fun v => (v.2.1, v.2.2.1, v.2.2.2.base.produced)` (post output, run ledger, produced frames). Premises: the read-backs and the run budget of `first`, for every `second` (no post budget: the post part issues only coins, HMAC and BLAKE2b and no field read, `compile_later_reads`).

- L-B1 draws and prefix (`PqxdhDeploymentIdealLaterParams`, `PqxdhDeploymentIdealLaterCut`, about 45-60 theorems). `slotGameL_pool` and `draws_swapL` (from `PqxdhDeploymentIdealParams.preOpaquePool`, `slotGame_pool`, `draws_swap` with `LaterServerOpaque.sourcePreOpaque`); `compile_scanServer` (the logged scan of `compileServer` is the compiled CE scan with LQ's finish pre-reads, `compileSnapImpl`; terminal reads, Server read and post part are in the continuation); the logged pool source `sourcePoolL` (`PqxdhDeploymentIdealPoolSource.sourcePool` on `.inl`, the logged accept, the read) and `commonPrefixL`; `ideal_cutL`, `ideal_prefixL`, `item2_prefixL` with `cutStateL` carrying the ghosts; `CutRelL := CutRel ∧ log on both sides equal ∧ compiled snapshot = native snapshot of the merge (PqxdhDeploymentLaterCompile.snapshot_merge)`. Reused: `PqxdhDeploymentIdealCut.preStep`, `preScan`, `compile_scan`, `pool_scan_source`, `stopped_scan_source`, `cut_rel`, `PqxdhDeploymentIdealPool.compile_simulation_pool`, `PqxdhDeploymentIdealBranch.CutRelIndexed`, `ideal_compile_of_selected`'s structure, `PqxdhDeploymentIdealActive.ActiveBranch`/`activeCE`, LQ's `snap_step`, `snap_good`.
- L-B2 middle run, continuation and assembly (`PqxdhDeploymentIdealLaterPost`, possibly split in two, and `PqxdhDeploymentIdealLaterCompile`, about 90-130 theorems). `MidL` (U6's `Mid` with snapshot and log), `sourceMidL` (logged `sourceMid`: the non-selected logged accept appends the same entry on both views, every quiet command keeps the log, `PqxdhDeploymentLaterServerGame.handler_quiet`, and updates the snapshot by `PqxdhDeploymentLater.snapshotAt`), `compiledMidL` with `compileSnapImpl`; `step_realL` from U6's `PqxdhDeploymentIdealPostSource.step_real` plus the ghost update; the selected accept from `PqxdhDeploymentIdealPostAccept.resume_accept` with the entry; `step_challenge` and the marked build reused (log quiet); field reads by `PqxdhDeploymentIdealPostRequests.step_read`; new `step_identity` and `step_serverRead` (identity-pool reveals through item 2's post-challenge router against the merged owners and the Server seed); `ItemInvL`, `keep_allL`, `item_simL` (U6's `item_sim` with `Allowed` widened to identity reads and the read, KEM reads still capped at 0 by `compile_server_no_kem`); `itemPost_middleL` and `activeCE_middleL` (the CE side is the run-phase merge image followed by `xreveal` and `realPost`); `server_continuationMid` (the terminal part and the read under `sourceMidL` return `xreveal` of the merged state and the post part is `realPost`, from LQ-F's `server_continuation`, `terminal_quiet`, `post_quiet` and LQ's `reveal_merge`); `decision_mergeL` (the LQ-F decision on `observeCompiled` and the CE decision on `observeLater` agree on the merge image; the designation is a run-phase fact, `PqxdhDeploymentIdealKeymatch.target_marked`); `GoodMidL` and `middleInvL` from `PqxdhDeploymentIdealPostGood.GoodMid`/`middleStart` (post commands and reads keep CE-3's `Good`, `PqxdhDeploymentLaterServerCompile.server_good`); `activeBranchL_of_middle`, `active_branchL`, `ideal_compile_later_of_active`, `ideal_compile_later`; and, once (c) is integrated, `ideal_world_later` (from `ideal_compile_later` and `c6_idealGame`, the later form of U7's `ideal_world`).

## 6. (c) Unit 11b-L (U-L3)

Statements of the generic part, elaborated in `probe/Stmts.lean` (`laterWith_param`, `join_later_param`, `c6_ideal`):

```lean
-- PqxdhDeploymentIdealLater (generic)
theorem postNative_real (reg) (hmacReal : ∀ created key message x, (reg created ⟨.hmac key message, trivial⟩).run x =
    (fun r => (r.1, { x with base := r.2 })) <$> (PqxdhDeploymentNative.handler setup codec checks route created.seed (.inr (.hmac key message))).run x.base)
    (created) (query) (x) : (postNative setup codec route (reg created) query).run x = (realPost setup codec checks created query).run x
theorem represent_later (core) (natural : CoreNatural core) … (postWith) (postNatural : ∀ q x, (postWith q).run (mapBackend proj x) = Prod.map id (mapBackend proj) <$> (postWith q).run x) :
  LawEq (outcomeMap (mapBackend proj) <$> (laterWith … init (core svc₁) postWith …).run runtime) ((laterWith … (proj ∘ init) (core svc₂) postWith …).run runtime)
theorem represent_split_later …          -- represent_later twice, as represent_split
theorem game_moveSeeds_later …           -- PqxdhDeploymentIdealKeys.game_moveSeeds for laterWith (realPost is seed-blind)
theorem laterWith_param (init) (regs : P → Created → RegImpl KemSK Bk n) (p) … :
  (laterWith … (fun c => (p, init c)) (fun c => paramReg (fun q => regs q c)) (fun c => postNative … (paramReg (fun q => regs q c))) …).run runtime =
    outcomeMap (withX p) <$> (laterWith … init (regs p) (fun c => postNative … (regs p c)) …).run runtime
theorem join_later_draw …                -- join_later with `born : env.start = draw >>= …` (join_draw's counted startup)
theorem join_later_param (draw) (init) (regs) (steps) … (stable) (startInv) (splits) … :
  LawEq (draw >>= fun p => (·.map fun v => (v.1, v.2.1, v.2.2.1, withX p v.2.2.2)) <$> (laterWith … init (regs p) (fun c => postNative … (regs p c)) …).run' runtime)
    (joined <$> PqxdhRecordLiftLater.run setup codec route (paramEnv setup draw steps ensureInit identityIndex runtime init) setup.serverKeyId bounds mode envReveal first second)
-- PqxdhDeploymentIdealLaterEnv (instances)
theorem erase_ideal_later …              -- erase_later_ctx at idealPair with realPost (realPost_commutes)
theorem represent_ideal_later / seed_move_later / ideal_to_splitX_later
theorem ideal_to_splitEager_later        -- rewrite by PqxdhDeploymentIdealKernel.split_kernel
theorem split_later                      -- defer_later at the pair of split_game, realPost_commutes_seed
theorem ideal_to_split_later             -- at splitView, the chain above
theorem c6_split / c6_ideal / c6_ideal_public / c6_idealGame   -- join_later_param with ideal_splits, as c1_split/c1_ideal/c1_idealGame
```

Route: the generic part copies `represent`, `game_moveSeeds`, `gameWith_param` (`handlerWith_param` with `xreveal (withX p y) = xreveal y`), `join_draw` and `join_later` to `laterWith`; the instances replay `ideal_to_split`'s chain (`erase_ideal`, `represent_ideal`, `seed_move`, `split_kernel`, `split_game`) with the fixed post handler `realPost` after `postNative_real` (instances from `idealProg_real` with `slotCore_lift`); `c6_*` replay `c1_*` with `join_later_param` and `ideal_splits`. `c4_ideal_later` and `frame_idealD` exist.

Optional L-C+ (U-L4 of the CE-12 design, `PqxdhDeploymentIdealLaterSlots`, about 8-15 theorems): `post_noinstall` (the post phase of `envGD`, coins, hashes and HMAC, installs no hidden kernel, so the slot map after the post phase is the run-phase one) and `later_slots` (on `laterRealChains env_g`, `IdealSlots` of the final view or the run-phase `Anomaly`, from `ideal_view_slots` of U7 and `PqxdhRecordLiftLaterWorlds.laterReal_event`). It needs U7 (`PqxdhDeploymentIdealHandoff`) integrated.

## 7. Modules, increments and order

All names below are unused (no file in any `/tmp/beaconcrypt-*` worktree or scratch, no root import), and all but the generic hybrid sit under the `PqxdhDeployment*` prefix registered to claude.

| Unit | Modules | Stages | Depends on |
| --- | --- | --- | --- |
| C | `PqxdhDeploymentIdealLater`, `PqxdhDeploymentIdealLaterEnv` (+ optional `PqxdhDeploymentIdealLaterSlots`) | (c), U-L4 | central; U-L4 also U7 |
| A1 | `PqxdhDeploymentLaterServerItemSkeleton`, `…ItemFree`, `…ItemShared`, `…ItemSplit` | L-A1 to L-A4 | central |
| A2 | `…ItemRoot`, `…ItemOnce`, `…ItemFactor`, `PqxdhDeploymentLaterServerItemHybrid`, `…ItemKeys`, `…ItemBills` | L-A5 to L-A9 | A1 |
| B1 | `PqxdhDeploymentIdealLaterParams`, `PqxdhDeploymentIdealLaterCut` | L-B1 | A2's definitions (`slotGameL`) |
| B2 | `PqxdhDeploymentIdealLaterPost` (one or two modules), `PqxdhDeploymentIdealLaterCompile` | L-B2 | B1; C for `ideal_world_later` |

Each unit is one publication unit on its own `claude/…` branch from freshly fetched central: one Lean commit per module (root import, inventory row, check-inventory block, `inv recount` before `inv rehash`), guards with exact `#guard_msgs` over `#print axioms` allowing only `propext`, `Classical.choice`, `Quot.sound`, statements in `𝒟[…]`, contamination scan (no DH-keyed component, no fixed-HKDF item), candidate-freedom closure check for `rootClientL`, `entryClientL`, `slotGameL`, then semantic and hygiene review, fix pass, confirming review and integration (protocol section 6). Order: C and A1 in parallel (two tracks), then A2, then B1 (may overlap A2's bills module), then B2. At most two heavy tracks at a time.

## 8. Effort (nominal agent-days)

Calibration: one working session is one agent-day and produces 100-200 guarded theorems (item 2 increments 133, 207, 127, 187+91; LQ-F spike 112; CE-11b U6 fourth part 101 and U4c 78 for simulation-heavy work). Lift and copy stages are counted at the upper half of that range, simulation-heavy stages at 80-110. Review, fix pass, confirming review and integration add 0.5-1 per publication unit.

| Unit | New theorems | Build | Review to integration | Total |
| --- | --- | --- | --- | --- |
| C (11b-L) | 30-40 | 0.3-0.5 | 0.5-1 | 1-1.5 |
| C+ (U-L4, optional here) | 8-15 | 0.1-0.2 | with C | +0.5 |
| A1 (L-A1 to L-A4) | 100-130 | 0.7-1.2 | 0.5-1 | 1.5-2.5 |
| A2 (L-A5 to L-A9) | 95-125 | 0.6-1 | 0.5-1 | 1.5-2.5 |
| B1 | 45-60 | 0.5-0.8 | 0.5 | 1-1.5 |
| B2 | 90-130 | 1-1.5 | 0.5-1 | 2-3 |
| Sum | 360-500 | | | 7-11 (+0.5) |

Against §49 Q1 (item 2 work 6-12, `ideal_compile_later` 6-10, 11b-L 2.5-5, total 14.5-27): (a) 3-5, (b) 3-4.5, (c) 1-1.5. The reduction comes from D2 (per-request reuse, one new case per layer), from CE-11b's ideal game already running the logged handler, and from the later erasure and deferral tools already on central. Risk-adjusted ceiling about 14 (R1, R4). Elapsed time with two tracks: about 5-8 days.

## 9. CE-12-L headlines unblocked

| Headline (CE-12 design §9.1) | Needs | Unblocked after |
| --- | --- | --- |
| CE-KT-L, transfer form `|Pr_LQF[D_g] − Pr_{IL_g}[D_g]| ≤ kemLossL + slotLossL` | `kem_transfer_server_two_sided` (exists), `later_slots_two` (A2), `ideal_compile_later` (B2) | A2 + B2 |
| CE-KT-L, world form | + `c6_idealGame` (C) | A2 + B2 + C |
| CE-APP-L | + U-L4 (C+), `later_record_lift`, `later_idealRecords_fresh` (exist), `anomaly_le_pk` (run phase) | A2 + B2 + C + C+ |
| CE-LOR-L | as CE-APP-L, with `later_idealRecords_lor` (exists); both events transferred per target, every step two-sided | A2 + B2 + C + C+ |
| Bills of the three | `laterSlot_bills` (A2), `kem_transfer_server_bills`, `c4_ideal_later` (exist) | A2 |
| Symbolic corollaries (`ε_A1`, `ε_A2pub`, `ε_ct`, `β_g`) | run-phase classical terms through `game_classical_event` | not blocked |

## 10. Risks and fallbacks

- R1 (elaboration under `-M8000`). The logged copies of S1b and S3b assemblies are the heaviest. Mitigation: keep the classical module split, state per-request lemmas separately, reuse classical per-request proofs through `acceptStepL_fst`-style projections. Fallback F-A (generic source extension, D1) costs +3-5.
- R2 (a classical lemma is not per-request). Some classical results are stated for the whole fixed handler (`opaqueBranch_grouped`, `groupedResume_split`, `skelImpl_run`, `commands_cut`); these are re-proved, already counted. If a per-request lemma hides a whole-handler argument, its logged copy is a proof copy (+0.5).
- R3 (stage T's collapse). `top_step`/`pre_step` are stated on the classical collapsed state; reuse needs a projection lemma for the log component. Fallback: copy the two step lemmas (+0.3).
- R4 (ghosts in U6's middle run). U5/U6 dropped the ghosts (`idealRun_unghost`); the later middle run carries them, so every middle step needs its ghost update. Non-accept commands keep the log and move the snapshot by `snapshotAt`, so their steps follow from the unghosted ones; the accept steps (selected and not) are re-proved with the entry. Fallback F-B: split `ideal_compile_later` at the end of the run part, proving a state form of the run-phase compile equality (joint law of the merged run-phase state, which `activeCE_middle` and `itemPost_middle` almost give) and appending the reveal and the post phase by `laterTail` congruence (+1-2).
- R5 (identity reads in the middle). U6's `Allowed` excluded identity reads; `compileServer` issues `qCreate` of them in its terminal part plus the Server read. `step_identity` and `step_serverRead` go through item 2's post-challenge router's identity pool; `PoolOwned` gives the slot-to-seed link. If the router's history makes the views differ, they are erased in item 2's view as U6 does for pool changes (`prepKnown_erase`).
- R6 (bills need a read cap). `rootClientL_coins` takes a cap on Server reads, as `LaterServerBills.adversary_bound` does; `compile_server_reads` meets it with one.
- R7 (name clashes). The lift reuses short names; every new declaration carries an `L` suffix or lives in its own namespace; consumers qualify, as the LQ-F guide asks.
- R8 (overclaim). Statements stay confidentiality-only; no T5, A2 or T8 on `compileServer`; R1's decorrelation caveat and `SourceFullCorrect`, HMAC-PRF and Extract-on-`uniform32` are listed exactly as for classical T7; the post queries are classical (no QPT, no QROM).

## 11. Probes run (scratch, central `66f425ef`)

- `probe/Names.lean`, `probe/Names2.lean`, `probe/Names3.lean`: 426 names checked by `Environment.contains`; 422 present as first written, 4 corrected to their namespaces (section 1). Logs `names.log`, `names2.log`, `names3.log`.
- `probe/SkelL.lean`: `AcceptL`, `GSpecL`, `acceptStepL`, `skelImplL`, `groupedClientL` elaborate; `acceptStepL_fst` is proved (no `sorry`, empty log `skel.log`).
- `probe/Stmts.lean`: `laterWith_param`, `join_later_param`, `idealLaterGame`, `c6_ideal`, `observeLater` and `ideal_compile_later` (with a `sorry` stub of `slotGameL` at its intended signature) elaborate; only `sorry` warnings (`stmts.log`).
- `probe/Hmac.lean`: `laterTransported bounds B post (.inl 3) + … (.inl 5) + … (.inl 6) = B.accept + B.finish + (B.hmac + post.hmac)` by `simp` (empty log `hmac.log`).

## 12. Assumptions and non-claims

No new assumption, contract or idealization. (a) uses route R1 (zero-key 192-byte Extract slice as a random oracle), the HMAC-SHA-512 PRF game, the Extract game on `uniform32`, `SourceFullCorrect setup.source setup.hmac` and the logged source budget; (b) and (c) use `Phase1ReadBack`, `Phase2ReadBack`, the run budget and, for bills, `KemBound` and `initBound`; the KEM step upstream uses `FunctionalDecapsulation` and ML-KEM IND-CCA as `kem_transfer_server` does. Nothing here claims authentication in the later mode, a QPT or QROM adversary, persistence, codec internals or primitive implementations; the two profile exceptions of plan §27 replace deviation D6 only when the headlines land (LQ-8).

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterCut
import BeaconcryptCore.Computational.PqxdhDeploymentIdealActive

/-! LQ-F upstream, unit B1: the branches of the later second compile lemma at the cut, and its reduction to the active branch (the logged counterpart of CE-11b unit U6's `PqxdhDeploymentIdealBranch` and `PqxdhDeploymentIdealActive`). `PqxdhDeploymentIdealLaterCut` cut both sides at the selected raw accept; this module splits the comparison at the cut into its branches, proves every branch except the active one, and reduces the frozen target `PqxdhDeploymentIdealLaterGame.IdealCompileServerTarget` to the active branch `ActiveBranchL` at every draw of the challenger (`ideal_compile_server_of_active`).

- The later decision reads the mark. `keymatch_later`: on every outcome of the later ideal game, a claim that designates `g` on the LQ-F outcome designates it on the run phase's ledger (the post phase adds no ledger entry), so by `PqxdhDeploymentIdealKeymatch.ideal_keymatch` on the run phase (through `PqxdhDeploymentIdealLaterGame.laterWith_split`) the selected session is marked, and the real post phase keeps the mark. Hence the later decision `ceDecideL` equals the decision together with the mark (`markedDecisionL`, `game_markedL`).
- Item 2's side at the cut: `itemPostL` (the logged skeleton's post-challenge phase with the factored services under item 2's public-table layer and the first-touch allocator), `itemRestL` (`opaqueAfterL`, then `itemPostL`), and `laterSlotGameAt_cut`: item 2's logged two-slot world at the draws is the Server birth, the common prefix and `itemRestL`.
- The branches without an active cut accept nothing on both sides: a failed construction (`itemPostL_failed`), a completed cut, and a pending cut whose raw bytes do not verify to the selected PQ key (`itemRestL_dead` through `opaqueAfterL_dead`, `rejectRunL_complete`, `run_map`, `itemPostL_dead`; `resumeL_dead` through `PqxdhDeploymentIdealKeymatch.handler_accept_inactive`, `run_settled` and `laterTail_marks`: the post phase keeps the mark).
- The selected-key cut: on both sides the native steps before encapsulation of the Server's seed come first (`opaqueAfterL_selected` and `itemRestL_selected` through `PqxdhDeploymentIdealActive.stopped_program` on the logged steps; `acceptStep_selectedL` and `resumeL_selected` at the canonical state at the cut with the LQ-F ghosts); a rejection there accepts nothing on both sides, and an ephemeral leads to item 2's logged post-challenge phase on the active cut (with the logged continuation `compiledNextL`: the compiled continuation, then the terminal reads, the Server read and the post part) against `activeCEL`.
- The run part's budget: `runBudget` (CE-3's costs plus the finish pre-reads at the transported command caps), `run_certified`, `runBudget_caps` (no identity or KEM read, `qCreate` creations) and `scan_certifiedL`.
- The reductions: `SelectedBranchL` and `ActiveBranchL` are `Prop` definitions (obligations of unit B, not premises of any published claim); `ideal_compile_server_of_selected` proves the frozen target's equation from the selected-key branch at every draw (the draws `PqxdhDeploymentIdealLaterParams.laterSlotGame_pool`, the prefixes `laterSlotGameAt_cut` and `PqxdhDeploymentIdealLaterCut.ideal_prefixL`, the key match, the dead branches, `PqxdhDeploymentIdealLaterCut.cut_relL`), `selected_of_activeL` derives the selected-key branch from the active one, and `ideal_compile_server_of_active` composes them.

Premises: the approved codec contracts `Phase1ReadBack` and `Phase2ReadBack` and the run-phase budget. No post budget is used: the post part makes no raw accept and no creation, and runs only after the cut or inside a branch that accepts nothing. These are program equalities, equalities in law and support facts. They charge nothing and make no security claim; `ideal_compile_server_of_active` is a reduction, not the later second compile lemma. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentCompile (Local merge compileImpl)
open PqxdhDeploymentLater (Snap PostSpec)
open PqxdhDeploymentLaterCompile (compileSnapImpl)
open PqxdhDeploymentLaterServerSource (Log embed)
open PqxdhDeploymentIdealCut (CutCE scanCE finishCE)
open PqxdhDeploymentIdealLaterGame (laterOf ceDecideL)
open PqxdhDeploymentIdealLaterCut (markedL cutStateL resumeL commonPrefixL opaqueAfterL)
open PqxdhRegistrationJointRevealCosts (sourceKind)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X : Type}

/-! ### The later decision reads the mark -/

section Decision
open PqxdhDeploymentBackend (XState handlerWith xinitial gameWith)
open PqxdhDeploymentIdealSteps (IdealBk TableState idealReg idealInit)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentFinishErasure (laterWith laterTail realPost)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLaterServerTransfer (happens designated)
open PqxdhDeploymentInterface (Budget FreshBounds Mode ModeSpec asModeO)
variable {A Out : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (checks : Checks)

/-- The later decision together with the mark: the LQ-F event happens, the claim designates `g`, and the selected session is marked. -/
noncomputable def markedDecisionL (budget : Budget) (event : Observed Out → Bool)
    (claim : Observed Out → Option PqxdhDeploymentInterface.Handle) (g : Fin budget.accept × Fin budget.capacity)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out ×
      PqxdhDeploymentLaterServerGame.LaterState KemSK) × A) (mark : Bool) : Bool :=
  decide (happens event outcome = true ∧
    designated setup.source.crypto codec setup.serverKeyId budget claim outcome = some g) && mark

/-- The key match of the later ideal game (`PqxdhDeploymentIdealKeymatch.ideal_keymatch` carried to `laterWith` through `PqxdhDeploymentIdealLaterGame.laterWith_split`): on every outcome, a claim that designates `g` on the LQ-F outcome designates it on the run phase's ledger, so the selected session is marked at the end of the run, and the real post phase keeps the mark. Premise: `Phase1ReadBack`. -/
theorem keymatch_later (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (budget : Budget)
    (g : Fin budget.accept × Fin budget.capacity) (p : Params KemSK budget.create) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (runtime : A)
    (claim : Observed Out → Option PqxdhDeploymentInterface.Handle)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × PqxdhDeploymentSecrecy.Ledger ×
      XState KemSK (IdealBk TableState) 2) × A)
    (supported : outcome ∈ support ((laterWith setup codec route idealInit
      (idealReg setup codec route checks (Target.ofCE budget g) p) (realPost setup codec checks) ensureInit 0 bounds mode
        first second).run runtime))
    (chosen : designated setup.source.crypto codec setup.serverKeyId budget claim (laterOf outcome) = some g) :
    markedL outcome = true := by
  rw [PqxdhDeploymentIdealLaterGame.laterWith_split, mem_support_bind_iff] at supported
  obtain ⟨born, bornMember, supported⟩ := supported
  rcases born with ⟨_ | created, after⟩
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    simp [laterOf, designated, PqxdhDeploymentLaterServerTransfer.observeGame] at chosen
  · dsimp only at supported
    rw [mem_support_bind_iff] at supported
    obtain ⟨run, runMember, supported⟩ := supported
    simp only [laterTail, PqxdhDeploymentIdealLaterCut.realPost_run, bind_map_left, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at supported
    obtain ⟨post, -, rfl⟩ := supported
    have game : (some (PqxdhRegistrationJointServerBirth.encode created, run.1.1, run.1.2, run.2), after) ∈ support
        ((gameWith setup codec route idealInit (idealReg setup codec route checks (Target.ofCE budget g) p) ensureInit 0
          bounds mode first).run runtime) := by
      simp only [gameWith, StateT.run, mem_support_bind_iff]
      exact ⟨(some created, after), bornMember, by rw [support_map]; exact ⟨run, runMember, rfl⟩⟩
    simp only [laterOf, designated, PqxdhDeploymentLaterServerTransfer.observeGame, Option.map_some,
      Option.bind_some, PqxdhDeploymentKemTransfer.target, PqxdhDeploymentBackend.laterView] at chosen
    obtain ⟨handle, -, designatedIn⟩ := Option.bind_eq_some_iff.mp chosen
    have marked := PqxdhDeploymentIdealKeymatch.ideal_keymatch setup codec route checks (Target.ofCE budget g) p phase1
      setup.serverKeyId ensureInit 0 bounds mode first runtime _ game (PqxdhRegistrationJointServerBirth.encode created)
      run.1.1 run.1.2 run.2 rfl handle
      (PqxdhDeploymentKemTransfer.designateIn_some setup.source.crypto codec setup.serverKeyId budget _ handle g
        designatedIn)
    exact marked

/-- With the key match, the later decision on the later game with the ideal registration at the target of `g` is the decision together with the mark (`keymatch_later`). Premise: `Phase1ReadBack`. -/
theorem game_markedL (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec) (budget : Budget)
    (event : Observed Out → Bool) (claim : Observed Out → Option PqxdhDeploymentInterface.Handle)
    (g : Fin budget.accept × Fin budget.capacity) (p : Params KemSK budget.create) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (runtime : A) :
    ceDecideL setup codec budget event claim g <$>
        (laterWith setup codec route idealInit (idealReg setup codec route checks (Target.ofCE budget g) p)
          (realPost setup codec checks) ensureInit 0 bounds mode first second).run runtime =
      (fun outcome => markedDecisionL setup codec budget event claim g (laterOf outcome) (markedL outcome)) <$>
        (laterWith setup codec route idealInit (idealReg setup codec route checks (Target.ofCE budget g) p)
          (realPost setup codec checks) ensureInit 0 bounds mode first second).run runtime := by
  apply PqxdhDeploymentKemTransfer.map_support_congr
  intro outcome member
  unfold ceDecideL markedDecisionL
  by_cases chosen : designated setup.source.crypto codec setup.serverKeyId budget claim (laterOf outcome) = some g
  · rw [keymatch_later setup codec route checks phase1 budget g p ensureInit bounds mode first second runtime claim
      outcome member chosen, Bool.and_true]
  · simp [chosen]

end Decision

/-! ### Item 2's side at the cut -/

section Item2
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhRegistrationJointKemEntryFactor (Output factoredServices publicLocalV)
open PqxdhDeploymentLaterServerOpaque (OpaqueContext OpaqueCut)
open PqxdhDeploymentSecrecy (Ledger wrap)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec asModeO)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count) {A Out : Type}
  (decision : Out × (Ledger × (Snap × Local)) → Bool)

/-- Item 2's logged post-challenge phase at the challenger's draws, from a logged prechallenge context: the logged skeleton's post-challenge phase with the factored services under item 2's public-table layer, from the table cache held by the context, then the first-touch allocator in front of item 2's two-slot table. -/
noncomputable def itemPostL (context : OpaqueContext Reader KemSK A (Out × (Ledger × (Snap × Local))) count) :
    ProbComp Bool :=
  (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl (D := PqxdhCorrelatedExtractFamily.Message)
      (PqxdhRegistrationJointKemSecondEntry.tableService (n := 2)))
    ((simulateQ (publicLocalV Output) (PqxdhDeploymentLaterServerItemTargets.postSkelL setup codec checks decision count
      t.kem (factoredServices setup codec checks) p.chosen p.challenge context)).run'
        (PqxdhDeploymentLaterServerItemTargets.cacheOfL context))).run'
    (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial)

/-- Item 2's side after the common prefix: the rest of item 2's logged opaque scan (`opaqueAfterL`), then the logged post-challenge phase on the resulting prechallenge context. -/
noncomputable def itemRestL (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (after : A)
    (reached : (CutCE (X × Ledger) × (Snap × Local)) × (PqxdhRegistrationJointSchedule.State KemSK × Log)) :
    ProbComp Bool :=
  opaqueAfterL setup codec route checks t p decision second created reached >>= fun result =>
    itemPostL setup codec checks t p decision (.ready created p.others result.1 result.2 after)

/-- Item 2's logged two-slot world at the challenger's draws (`PqxdhDeploymentIdealLaterParams.laterSlotGameAt`), for the compiled LQ-F program, is the Server construction, then on a constructed Server the common prefix (`commonPrefixL`) and `itemRestL`, and on a failed construction the post-challenge phase of the failed context. Premises: a budget of the compiled scan of the run part that reads no identity or KEM field and creates no more KEM keys than the pool holds (those of `PqxdhDeploymentIdealLaterCut.item2_prefixL`). -/
theorem laterSlotGameAt_cut (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (runtime : A)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → ℕ)
    (certified : ∀ source, (PqxdhDeploymentIdealLaterCut.compileCutSnap setup codec route <$>
      (simulateQ (compileSnapImpl setup codec route) (scanCE (wrap setup.source.crypto codec setup.serverKeyId bounds
        (asModeO mode first)) t.accept)).run (Snap.empty, Local.empty)).IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = source) (budget source))
    (unreadIdentity : budget (.inr 0) = 0) (unreadKem : budget (.inr 1) = 0)
    (room : budget (.inl 1) ≤ (p.pool t).length) :
    PqxdhDeploymentIdealLaterParams.laterSlotGameAt (Reader := Reader) setup codec checks ensureInit none decision
        (PqxdhDeploymentLaterServerCompile.compileServer setup codec route bounds mode first second) runtime count t.kem
        t.accept 2 p =
      (PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId none).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) >>= fun born =>
        match born.1 with
        | none => itemPostL setup codec checks t p decision (.failed born.2)
        | some created =>
            commonPrefixL setup codec route checks t p created born.2.1
                (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first)) >>= fun reached =>
              itemRestL setup codec route checks t p decision second (PqxdhRegistrationJointServerBirth.encode created)
                born.2.2 reached := by
  unfold PqxdhDeploymentIdealLaterParams.laterSlotGameAt PqxdhDeploymentIdealLaterParams.entryClientAtL
  rw [PqxdhDeploymentIdealParams.internalize_run]
  unfold PqxdhDeploymentIdealLaterParams.startPoolL
  rw [bind_assoc]
  simp only [pure_bind]
  rw [PqxdhDeploymentIdealLaterCut.item2_prefixL setup codec route checks t p ensureInit decision bounds mode first second
    runtime budget certified unreadIdentity unreadKem room, bind_assoc]
  refine bind_congr fun born => ?_
  rcases born with ⟨_ | created, after⟩
  · simp only [pure_bind]
    rfl
  · simp only [bind_assoc, pure_bind]
    rfl

/-- On a failed construction, item 2's logged post-challenge phase accepts nothing. -/
theorem itemPostL_failed (state : PqxdhRegistrationJointServerPrefix.State KemSK A) :
    itemPostL setup codec checks t p decision (.failed state) = pure false := by
  simp only [itemPostL, PqxdhDeploymentLaterServerItemTargets.postSkelL, simulateQ_pure, StateT.run'_eq,
    StateT.run_pure, map_pure]

/-- Item 2's logged post-challenge phase accepts nothing on a prechallenge context without an active cut at the selected PQ key: a stopped run, a completed run, or a cut whose verified PQ key is not the selected one. -/
theorem itemPostL_dead (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit)
    (cut : Option (OpaqueCut Reader KemSK (Out × (Ledger × (Snap × Local))) Bool))
    (state : PqxdhDynamicKemJointSource.State KemSK) (after : A)
    (dead : ∀ raw value ephemeral consumed native owners log next,
      cut = some (.pending raw value ephemeral consumed native owners log next) → value.keys.pqKey ≠ p.chosen.1) :
    itemPostL setup codec checks t p decision (.ready created p.others cut state after) = pure false := by
  rcases cut with _ | (outcome | ⟨raw, value, ephemeral, consumed, native, owners, log, next⟩)
  · simp only [itemPostL, PqxdhDeploymentLaterServerItemTargets.postSkelL, simulateQ_pure, StateT.run'_eq,
      StateT.run_pure, map_pure]
  · simp only [itemPostL, PqxdhDeploymentLaterServerItemTargets.postSkelL, simulateQ_pure, StateT.run'_eq,
      StateT.run_pure, map_pure]
  · have other := dead raw value ephemeral consumed native owners log next rfl
    simp only [itemPostL, PqxdhDeploymentLaterServerItemTargets.postSkelL, other, ↓reduceIte, simulateQ_pure,
      StateT.run'_eq, StateT.run_pure, map_pure]

end Item2

/-! ### The branches without an active cut -/

section Dead
open PqxdhDeploymentBackend (XState handlerWith)
open PqxdhDeploymentIdealSteps (IdealBk TableState idealReg idealInit)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentFinishErasure (laterTail realPost)
open PqxdhDeploymentLaterServerOpaque (OpaqueCut rejectRun)
open PqxdhDeploymentSecrecy (Ledger)
open LazyOracleDiscard (LawEq)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count) {A Out : Type}

/-- The completion of a raw accept by the logged `rejectRun` is never a pending cut. -/
theorem rejectRunL_complete {Z R : Type} (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (observe : Z × PqxdhRegistrationJointAcceptCutTag.Tag → R) (raw : Pqxdh.Bytes)
    (next : Option ℕ → OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) Z)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (log : Log)
    (state : PqxdhServerAuthNative.NativeState KemSK)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes) (logged : Option PqxdhJointGapDh.ScalarBytes)
    (cut : OpaqueCut Reader KemSK Z R)
    (member : cut ∈ support (rejectRun setup codec checks identityIndex publicIdentity observe raw next owners log state
      collected logged)) :
    ∃ outcome, cut = .complete outcome := by
  unfold rejectRun at member
  rw [mem_support_bind_iff] at member
  obtain ⟨_, -, member⟩ := member
  rw [support_map] at member
  obtain ⟨outcome, -, rfl⟩ := member
  exact ⟨outcome, rfl⟩

/-- The logged command run of a mapped program is the run of the program with its result mapped. -/
theorem run_map {Z W : Type} (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity) (f : Z → W)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) Z)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (log : Log)
    (state : PqxdhServerAuthNative.NativeState KemSK) :
    PqxdhDeploymentLaterServerCommands.run setup codec checks identityIndex publicIdentity (f <$> work) owners log state =
      (fun result => ((f result.1.1, result.1.2), result.2)) <$>
        PqxdhDeploymentLaterServerCommands.run setup codec checks identityIndex publicIdentity work owners log state := by
  simp only [PqxdhDeploymentLaterServerCommands.run, simulateQ_map, StateT.run_map]

/-- The rest of item 2's logged opaque scan after the common prefix has an active cut at the selected PQ key only from a pending compiled cut whose raw bytes verify to that key. -/
theorem opaqueAfterL_dead (decision : Out × (Ledger × (Snap × Local)) → Bool)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit)
    (reached : (CutCE (X × Ledger) × (Snap × Local)) × (PqxdhRegistrationJointSchedule.State KemSK × Log))
    (dead : ∀ raw next, reached.1.1 = .pending raw next → ∀ value,
      PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value → value.keys.pqKey ≠ p.chosen.1)
    (result : Option (OpaqueCut Reader KemSK (Out × (Ledger × (Snap × Local))) Bool) ×
      PqxdhDynamicKemJointSource.State KemSK)
    (member : result ∈ support (opaqueAfterL setup codec route checks t p decision second created reached)) :
    ∀ raw value ephemeral consumed native owners log next,
      result.1 = some (.pending raw value ephemeral consumed native owners log next) → value.keys.pqKey ≠ p.chosen.1 := by
  intro raw value ephemeral consumed native owners log next found
  have produced := PqxdhDeploymentIdealBranch.optionRun_support _ _ _ result member _ found
  rw [mem_support_bind_iff] at produced
  obtain ⟨logged, loggedMember, produced⟩ := produced
  rcases reached with ⟨⟨cutCE, snap, copies⟩, joint, logAt⟩
  rcases cutCE with run | ⟨raw0, next0⟩
  · simp only [PqxdhDeploymentIdealLaterCut.compileCutSnap, PqxdhDeploymentIdealLaterCut.scanRest, run_map,
      simulateQ_map, support_map, Set.mem_image] at loggedMember
    obtain ⟨inner, -, rfl⟩ := loggedMember
    simp [PqxdhDeploymentIdealLaterCut.opaqueRestL] at produced
  · simp only [PqxdhDeploymentIdealLaterCut.compileCutSnap, PqxdhDeploymentIdealLaterCut.scanRest,
      PqxdhDeploymentLaterServerCommands.run, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at loggedMember
    subst loggedMember
    unfold PqxdhDeploymentIdealLaterCut.opaqueRestL at produced
    rcases found : PqxdhRegistrationJointRawSignatures.verified setup codec checks raw0 with _ | verified
    · simp only [found] at produced
      obtain ⟨outcome, impossible⟩ := rejectRunL_complete setup codec checks _ _ _ _ _ _ _ _ _ _ _ produced
      cases impossible
    · simp only [found, mem_support_bind_iff] at produced
      obtain ⟨prepared, -, produced⟩ := produced
      split at produced
      · obtain ⟨outcome, impossible⟩ := rejectRunL_complete setup codec checks _ _ _ _ _ _ _ _ _ _ _ produced
        cases impossible
      · rw [support_pure, Set.mem_singleton_iff] at produced
        injection produced with sameRaw sameValue
        subst sameValue
        exact dead raw0 next0 rfl _ found

/-- Item 2's side accepts with probability zero (in law, it is `pure false`) when the CE cut is complete or its raw bytes do not verify to the selected PQ key. -/
theorem itemRestL_dead (decision : Out × (Ledger × (Snap × Local)) → Bool)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (after : A)
    (reached : (CutCE (X × Ledger) × (Snap × Local)) × (PqxdhRegistrationJointSchedule.State KemSK × Log))
    (dead : ∀ raw next, reached.1.1 = .pending raw next → ∀ value,
      PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value → value.keys.pqKey ≠ p.chosen.1) :
    LawEq (itemRestL (Reader := Reader) setup codec route checks t p decision second created after reached)
      (pure false) := by
  unfold itemRestL
  refine (PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun result member => LawEq.of_eq
    (itemPostL_dead setup codec checks t p decision created result.1 result.2 after
      (opaqueAfterL_dead setup codec route checks t p decision second created reached dead result member))).trans
    (LazyOracleDiscard.lawEq_drop _ _)

/-- Every outcome of the real post phase from a state keeps that state's mark. -/
theorem laterTail_marks (created : PqxdhLiveServerConstruction.Created Unit)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (after : A)
    (value : X × Ledger) (x : XState KemSK (IdealBk TableState) 2)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × Ledger ×
      XState KemSK (IdealBk TableState) 2) × A)
    (member : outcome ∈ support (laterTail (realPost setup codec checks) created second id after (value, x))) :
    markedL outcome = x.backend.2.2.marks.isSome := by
  simp only [laterTail, PqxdhDeploymentIdealLaterCut.realPost_run, bind_map_left, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at member
  obtain ⟨post, -, rfl⟩ := member
  rfl

/-- The CE side accepts with probability zero (in law, it is `pure false`) when the cut is complete or its raw bytes do not verify to the selected PQ key: the canonical state at the cut marks no session, the selected accept is then the logged accept and leaves no mark, no later run step changes the mark (`PqxdhDeploymentIdealKeymatch.handler_accept_inactive`, `run_settled`), and the real post phase keeps it (`laterTail_marks`). -/
theorem resumeL_dead (created : PqxdhLiveServerConstruction.Created Unit)
    (decision : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out ×
      PqxdhDeploymentLaterServerGame.LaterState KemSK) × A → Bool)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (after : A)
    (cut : CutCE (X × Ledger)) (view : Snap × (PqxdhDeploymentNative.State KemSK × Log))
    (dead : ∀ raw next, cut = .pending raw next → ∀ value,
      PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value → value.keys.pqKey ≠ p.chosen.1) :
    LawEq (resumeL setup codec route checks t p created (fun outcome mark => decision outcome && mark) second after cut
      view) (pure false) := by
  unfold resumeL
  apply PqxdhDeploymentIdealBranch.map_const_lawEq
  intro outcome member
  rw [mem_support_bind_iff] at member
  obtain ⟨run, runMember, member⟩ := member
  rw [laterTail_marks setup codec checks created second after run.1 run.2 outcome member]
  suffices unmarked : run.2.backend.2.2.marks = none by
    simp only [unmarked, Option.isSome_none, Bool.and_false]
  rcases cut with result | ⟨raw, next⟩
  · simp only [finishCE, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at runMember
    subst runMember
    rfl
  · simp only [finishCE, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at runMember
    obtain ⟨accepted, acceptedMember, runMember⟩ := runMember
    obtain ⟨accepts, marks⟩ := PqxdhDeploymentIdealKeymatch.handler_accept_inactive setup codec route checks t p created
      raw (dead raw next rfl) (cutStateL t created view) rfl accepted acceptedMember
    have settled := PqxdhDeploymentIdealKeymatch.run_settled setup codec route checks t p created (next accepted.1)
      accepted.2 (by rw [accepts]; exact Nat.lt_succ_self _) run runMember
    rw [settled, marks]

end Dead

/-! ### Both sides at a selected-key cut -/

section Selected
open PqxdhServerRootPreparation (Verified)
open PqxdhDeploymentBackend (XState handlerWith)
open PqxdhDeploymentIdealSteps (IdealBk TableState idealReg idealInit)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentFinishErasure (laterTail realPost)
open PqxdhDeploymentLaterServerOpaque (OpaqueCut rejectRun)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentIdealActive (selectedStep acceptAfter)
open LazyOracleDiscard (LawEq)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count) {A Out : Type}

/-- The logged continuation of a pending compiled cut: the compiled continuation of the deployment program (`PqxdhDeploymentIdealLaterCut.compileCutSnap`), embedded, then the rest of the compiled LQ-F program. -/
noncomputable def compiledNextL (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out)
    (raw : Pqxdh.Bytes) (next : Option ℕ → OracleComp Spec (X × Ledger)) (state : Snap × Local) :
    Option ℕ → OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) (Out × (Ledger × (Snap × Local))) :=
  fun answer => simulateQ embed ((simulateQ (compileSnapImpl setup codec route) (next answer)).run
    (state.1, { state.2 with log := PqxdhDeploymentCompile.logReply state.2.log (.accept raw) answer })) >>=
      PqxdhDeploymentIdealLaterCut.restOf setup codec route second

/-- The rest of item 2's logged opaque scan after the common prefix at a pending CE cut whose raw bytes verify, under the stopped router: the native steps before encapsulation of any seed (`PqxdhDeploymentIdealActive.stopped_program`), then a rejection before encapsulation completes the run, and an ephemeral saves the active cut with the log at the cut, with the router state kept. -/
theorem opaqueAfterL_selected (decision : Out × (Ledger × (Snap × Local)) → Bool)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit)
    (reached : (CutCE (X × Ledger) × (Snap × Local)) × (PqxdhRegistrationJointSchedule.State KemSK × Log))
    (raw : Pqxdh.Bytes) (next : Option ℕ → OracleComp Spec (X × Ledger)) (pending : reached.1.1 = .pending raw next)
    (value : Verified Reader) (verified : PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value)
    (seed : PqxdhJointIdentity.IdentitySeed) :
    opaqueAfterL setup codec route checks t p decision second created reached =
      (simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup codec checks seed)
          (PqxdhDeploymentLaterServerSource.beforeLogged (Shared := PqxdhBeaconPhase2Preparation.Word32) value)).run
          reached.2.1.shared.2.server.consumed >>= fun pre =>
        match pre.1.1 with
        | none => ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem t.kem.val
            (p.pool t)) (rejectRun setup codec checks created.server.server.metadata.identityIndex created.publicIdentity
              (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw
              (compiledNextL setup codec route second raw next reached.1.2)
              (PqxdhRegistrationJointGeneratedFinish.encodeState setup reached.2.1).owners reached.2.2 reached.2.1.shared
              (none, pre.2) pre.1.2)).run).run
            (reached.2.1.pool.1, PqxdhDeploymentIdealPoolSource.routerOf reached.2.1.pool.2)
        | some ephemeral => pure (some (.pending raw value ephemeral pre.2 reached.2.1.shared
            (PqxdhRegistrationJointGeneratedFinish.encodeState setup reached.2.1).owners reached.2.2
            (compiledNextL setup codec route second raw next reached.1.2)),
            (reached.2.1.pool.1, PqxdhDeploymentIdealPoolSource.routerOf reached.2.1.pool.2)) := by
  rcases reached with ⟨⟨cut, snap, copies⟩, joint, logAt⟩
  simp only at pending
  subst pending
  simp only [opaqueAfterL, PqxdhDeploymentIdealLaterCut.compileCutSnap, PqxdhDeploymentIdealLaterCut.scanRest,
    PqxdhDeploymentLaterServerCommands.run, simulateQ_pure, StateT.run_pure, pure_bind,
    PqxdhDeploymentIdealLaterCut.opaqueRestL, verified]
  rw [simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind,
    PqxdhDeploymentIdealActive.stopped_program setup codec checks _ raw seed t.kem.val (p.pool t) _
      (PqxdhDeploymentIdealActive.beforeLogged_plain value) _ _, bind_map_left]
  refine bind_congr fun pre => ?_
  rcases pre with ⟨⟨_ | ephemeral, logged⟩, consumed⟩
  · rfl
  · simp only [Option.elim, simulateQ_pure, OptionT.run_pure, StateT.run_pure]
    rfl

/-- Item 2's side at a pending CE cut whose raw bytes verify (in law): the native steps before encapsulation of any seed, then on a rejection before encapsulation nothing is accepted, and on an ephemeral item 2's logged post-challenge phase runs on the active cut with the router state of the cut. -/
theorem itemRestL_selected (decision : Out × (Ledger × (Snap × Local)) → Bool)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (after : A)
    (reached : (CutCE (X × Ledger) × (Snap × Local)) × (PqxdhRegistrationJointSchedule.State KemSK × Log))
    (raw : Pqxdh.Bytes) (next : Option ℕ → OracleComp Spec (X × Ledger)) (pending : reached.1.1 = .pending raw next)
    (value : Verified Reader) (verified : PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value)
    (seed : PqxdhJointIdentity.IdentitySeed) :
    LawEq (itemRestL (Reader := Reader) setup codec route checks t p decision second created after reached)
      ((simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup codec checks seed)
          (PqxdhDeploymentLaterServerSource.beforeLogged (Shared := PqxdhBeaconPhase2Preparation.Word32) value)).run
          reached.2.1.shared.2.server.consumed >>= fun pre =>
        match pre.1.1 with
        | none => pure false
        | some ephemeral => itemPostL setup codec checks t p decision
            (.ready created p.others (some (.pending raw value ephemeral pre.2 reached.2.1.shared
              (PqxdhRegistrationJointGeneratedFinish.encodeState setup reached.2.1).owners reached.2.2
              (compiledNextL setup codec route second raw next reached.1.2)))
              (reached.2.1.pool.1, PqxdhDeploymentIdealPoolSource.routerOf reached.2.1.pool.2) after)) := by
  unfold itemRestL
  rw [opaqueAfterL_selected setup codec route checks t p decision second created reached raw next pending value verified
    seed, bind_assoc]
  refine PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun pre _ => ?_
  rcases pre with ⟨⟨_ | ephemeral, logged⟩, consumed⟩
  · refine (PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun result member => LawEq.of_eq
      (itemPostL_dead setup codec checks t p decision created result.1 result.2 after ?_)).trans
      (LazyOracleDiscard.lawEq_drop _ _)
    intro raw' value' ephemeral' consumed' native' owners' log' next' found
    have produced := PqxdhDeploymentIdealBranch.optionRun_support _ _ _ result member _ found
    obtain ⟨outcome, impossible⟩ := rejectRunL_complete setup codec checks _ _ _ _ _ _ _ _ _ _ _ produced
    cases impossible
  · simp only [pure_bind]
    exact LawEq.refl _

/-- The selected accept at the canonical state at the cut with the LQ-F ghosts, on raw bytes that verify to the selected PQ key: the native steps before encapsulation, then either the inactive accept tail or the steps after encapsulation (`PqxdhDeploymentIdealActive.acceptStep_selected` for `cutStateL`). -/
theorem acceptStep_selectedL (created : PqxdhLiveServerConstruction.Created Unit)
    (view : Snap × (PqxdhDeploymentNative.State KemSK × Log)) (raw : Pqxdh.Bytes) (value : Verified Reader)
    (verified : PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value)
    (matched : value.keys.pqKey = p.chosen.1) :
    (PqxdhDeploymentIdealSteps.acceptStep setup codec route checks t p created raw).run
        (PqxdhDeploymentIdealSlots.detach (cutStateL t created view)) =
      PqxdhDeploymentIdealSteps.liftS ((simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup codec checks created.seed)
          (PqxdhDeploymentLaterServerSource.beforeLogged (Shared := PqxdhBeaconPhase2Preparation.Word32) value)).run
          view.2.1.native.shared.2.server.consumed) >>= fun pre =>
        match pre.1.1 with
        | none => (selectedStep (fun s => do
            let r ← PqxdhDeploymentIdealSteps.liftS ((PqxdhRegistrationJointServerAccept.tail (Reader := Reader) setup
              (setup.joint.publicKeys created.seed) s.2 (none, pre.2)).run s)
            pure (((r.1, pre.1.2), (false, none)), r.2))).run
              (PqxdhDeploymentIdealSlots.detach (cutStateL t created view))
        | some ephemeral => (selectedStep (acceptAfter setup codec checks created.seed p.challenge value ephemeral pre.2
            pre.1.2)).run (PqxdhDeploymentIdealSlots.detach (cutStateL t created view)) := by
  have selected : (PqxdhDeploymentIdealSteps.acceptStep setup codec route checks t p created raw).run
      (PqxdhDeploymentIdealSlots.detach (cutStateL t created view)) =
      (selectedStep (PqxdhDeploymentIdealSteps.acceptExposed setup codec checks created.seed p.chosen p.challenge raw)).run
        (PqxdhDeploymentIdealSlots.detach (cutStateL t created view)) := by
    have counter : (PqxdhDeploymentIdealSlots.detach (cutStateL t created view)).backend.accepts = t.accept := by
      simp [PqxdhDeploymentIdealSlots.detach, cutStateL, PqxdhDeploymentIdealCut.withAccepts]
    change (if (PqxdhDeploymentIdealSlots.detach (cutStateL t created view)).backend.accepts = t.accept then _
      else _) = _
    simp only [counter, ↓reduceIte]
    rfl
  rw [selected]
  simp only [PqxdhDeploymentIdealSteps.acceptExposed, verified, matched, ↓reduceIte]
  change _ <$> (PqxdhDeploymentIdealSteps.liftS _ >>= _) = _
  rw [map_bind]
  refine bind_congr fun pre => ?_
  rcases pre with ⟨⟨_ | ephemeral, logged⟩, consumed⟩
  · rfl
  · rfl

/-- The CE side of an active selected accept at the cut, from the steps after encapsulation: the selected accept with `acceptAfter` through the first-touch allocator of the canonical state at the cut with the LQ-F ghosts, the continuation of the deployment program with the ideal registration, then the real post phase, read by a decision on the LQ-F outcome and the mark. -/
noncomputable def activeCEL (created : PqxdhLiveServerConstruction.Created Unit)
    (decision : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out ×
      PqxdhDeploymentLaterServerGame.LaterState KemSK) × A → Bool → Bool)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (after : A)
    (view : Snap × (PqxdhDeploymentNative.State KemSK × Log)) (next : Option ℕ → OracleComp Spec (X × Ledger))
    (value : Verified Reader) (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (logged : Option PqxdhJointGapDh.ScalarBytes) : ProbComp Bool :=
  (fun outcome => decision (laterOf outcome) (markedL outcome)) <$>
    (((fun r => (r.1.1, PqxdhDeploymentIdealSlots.attach r.1.2 r.2.1 r.2.2)) <$>
      (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
        ((selectedStep (acceptAfter setup codec checks created.seed p.challenge value ephemeral consumed logged)).run
          (PqxdhDeploymentIdealSlots.detach (cutStateL t created view)))).run
        ((cutStateL t created view).backend.2.1, (cutStateL t created view).backend.1) >>= fun r =>
      (simulateQ (handlerWith setup codec route (idealReg setup codec route checks t p created)) (next r.1)).run r.2) >>=
      laterTail (realPost setup codec checks) created second id after)

/-- The CE side at a pending cut whose raw bytes verify to the selected PQ key (in law): the native steps before encapsulation of the Server's seed, then on a rejection before encapsulation nothing is accepted (the selected accept is inactive and leaves no mark, which no later step and not the post phase changes), and on an ephemeral the active form `activeCEL`. -/
theorem resumeL_selected (created : PqxdhLiveServerConstruction.Created Unit)
    (decision : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out ×
      PqxdhDeploymentLaterServerGame.LaterState KemSK) × A → Bool)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (after : A)
    (view : Snap × (PqxdhDeploymentNative.State KemSK × Log)) (raw : Pqxdh.Bytes)
    (next : Option ℕ → OracleComp Spec (X × Ledger)) (value : Verified Reader)
    (verified : PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value)
    (matched : value.keys.pqKey = p.chosen.1) :
    LawEq (resumeL setup codec route checks t p created (fun outcome mark => decision outcome && mark) second after
        (.pending raw next) view)
      ((simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup codec checks created.seed)
          (PqxdhDeploymentLaterServerSource.beforeLogged (Shared := PqxdhBeaconPhase2Preparation.Word32) value)).run
          view.2.1.native.shared.2.server.consumed >>= fun pre =>
        match pre.1.1 with
        | none => pure false
        | some ephemeral => activeCEL setup codec route checks t p created
            (fun outcome mark => decision outcome && mark) second after view next value ephemeral pre.2 pre.1.2) := by
  have accept : (handlerWith setup codec route (idealReg setup codec route checks t p created) (.inr (.accept raw))).run
        (cutStateL t created view) =
      (simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup codec checks created.seed)
          (PqxdhDeploymentLaterServerSource.beforeLogged (Shared := PqxdhBeaconPhase2Preparation.Word32) value)).run
          view.2.1.native.shared.2.server.consumed >>= fun pre =>
        (fun r => (r.1.1, PqxdhDeploymentIdealSlots.attach r.1.2 r.2.1 r.2.2)) <$>
          (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
            (match pre.1.1 with
            | none => (selectedStep (fun s => do
                let r ← PqxdhDeploymentIdealSteps.liftS ((PqxdhRegistrationJointServerAccept.tail (Reader := Reader) setup
                  (setup.joint.publicKeys created.seed) s.2 (none, pre.2)).run s)
                pure (((r.1, pre.1.2), (false, none)), r.2))).run
                  (PqxdhDeploymentIdealSlots.detach (cutStateL t created view))
            | some ephemeral => (selectedStep (acceptAfter setup codec checks created.seed p.challenge value ephemeral
                pre.2 pre.1.2)).run (PqxdhDeploymentIdealSlots.detach (cutStateL t created view)))).run
            ((cutStateL t created view).backend.2.1, (cutStateL t created view).backend.1) := by
    change (PqxdhDeploymentIdealSlots.slotCore _ PqxdhDeploymentSeedSplit.tableService created
      ⟨.accept raw, trivial⟩).run (cutStateL t created view) = _
    rw [PqxdhDeploymentIdealSlots.slotCore_run]
    change (fun r => (r.1.1, PqxdhDeploymentIdealSlots.attach r.1.2 r.2.1 r.2.2)) <$>
      (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
        ((PqxdhDeploymentIdealSteps.acceptStep setup codec route checks t p created raw).run
          (PqxdhDeploymentIdealSlots.detach (cutStateL t created view)))).run
        ((cutStateL t created view).backend.2.1, (cutStateL t created view).backend.1) = _
    rw [acceptStep_selectedL setup codec route checks t p created view raw value verified matched, simulateQ_bind,
      StateT.run_bind, PqxdhDeploymentIdealCut.slotImpl_lift, bind_map_left, map_bind]
  unfold resumeL
  simp only [finishCE, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rw [accept, bind_assoc, bind_assoc, map_bind]
  refine PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun pre _ => ?_
  rcases pre with ⟨⟨_ | ephemeral, logged⟩, consumed⟩
  · change LawEq _ (pure false)
    apply PqxdhDeploymentIdealBranch.map_const_lawEq
    intro outcome member
    rw [mem_support_bind_iff] at member
    obtain ⟨reached, reachedMember, member⟩ := member
    rw [support_map] at reachedMember
    obtain ⟨inner, innerMember, rfl⟩ := reachedMember
    rw [mem_support_bind_iff] at member
    obtain ⟨run, runMember, member⟩ := member
    rw [laterTail_marks setup codec checks created second after run.1 run.2 outcome member]
    have produced : inner.1 ∈ support ((selectedStep (fun s => do
        let r ← PqxdhDeploymentIdealSteps.liftS ((PqxdhRegistrationJointServerAccept.tail (Reader := Reader) setup
          (setup.joint.publicKeys created.seed) s.2 (none, consumed)).run s)
        pure (((r.1, logged), (false, none)), r.2))).run
          (PqxdhDeploymentIdealSlots.detach (cutStateL t created view))) := by
      apply OracleComp.support_simulateQ_run'_subset
        (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService) _
        ((cutStateL t created view).backend.2.1, (cutStateL t created view).backend.1)
      rw [StateT.run'_eq, support_map]
      exact ⟨inner, innerMember, rfl⟩
    unfold selectedStep at produced
    rw [StateT.run, support_map] at produced
    obtain ⟨result, resultMember, same⟩ := produced
    dsimp only [StateT.run] at resultMember
    rw [mem_support_bind_iff] at resultMember
    obtain ⟨_, _, resultMember⟩ := resultMember
    rw [support_pure, Set.mem_singleton_iff] at resultMember
    subst resultMember
    have marks : inner.1.2.backend.marks = none := by rw [← same]
    have accepts : inner.1.2.backend.accepts = t.accept + 1 := by
      rw [← same]
      simp [PqxdhDeploymentIdealSlots.detach, cutStateL, PqxdhDeploymentIdealCut.withAccepts]
    have settled := PqxdhDeploymentIdealKeymatch.run_settled setup codec route checks t p created (next inner.1.1)
      (PqxdhDeploymentIdealSlots.attach inner.1.2 inner.2.1 inner.2.2)
      (by change t.accept < inner.1.2.backend.accepts; rw [accepts]; exact Nat.lt_succ_self _) run runMember
    rw [settled]
    change (decision _ && (inner.1.2.backend.marks).isSome) = false
    rw [marks]
    exact Bool.and_false _
  · simp only [bind_map_left]
    exact LawEq.of_eq (by simp only [activeCEL, bind_map_left, bind_assoc])

end Selected

/-! ### The CE budget of the run part -/

section Budget
open PqxdhDeploymentInterface (Budget FreshBounds Mode ModeSpec asModeO)
open PqxdhDeploymentSecrecy (wrap)
open PqxdhDeploymentLaterCompile (laterCost runCap)

/-- The source caps of the compiled run part of the LQ-F program: CE-3's per-command costs plus the finish pre-reads, at the transported command caps of the wrapped run-phase adversary (the run part of `PqxdhDeploymentLaterCompile.compile_later_bound`). -/
def runBudget (bounds : FreshBounds) (budget : Budget) (kind : PqxdhRegistrationJointRevealCosts.SourceKind) : ℕ :=
  ∑ core, laterCost kind core * runCap bounds budget core

/-- The compiled run part meets its caps, for a run-phase adversary within its budget. -/
theorem run_certified (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects first)
    (kind : PqxdhRegistrationJointRevealCosts.SourceKind) :
    ((simulateQ (compileSnapImpl setup codec route) (wrap setup.source.crypto codec setup.serverKeyId bounds
        (asModeO mode first))).run (Snap.empty, Local.empty)).IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = kind) (runBudget bounds budget kind) :=
  FinitePartitionQueryBounds.weighted_bound PqxdhDeploymentCompileBudget.commandKind (laterCost kind)
    (runCap bounds budget) (compileSnapImpl setup codec route) (fun query => sourceKind (KemSK := KemSK) query = kind)
    (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first))
    (fun core => PqxdhDeploymentCompileSecrecy.wrap_bound setup.source.crypto codec setup.serverKeyId bounds mode first
      budget respects core)
    (fun query state => PqxdhDeploymentLaterCompile.snap_step_bound setup codec route kind query state)
    (Snap.empty, Local.empty)

/-- The compiled run part reads no identity or KEM field, and creates at most the budget's creations. -/
theorem runBudget_caps (bounds : FreshBounds) (budget : Budget) :
    runBudget bounds budget (.inr 0) = 0 ∧ runBudget bounds budget (.inr 1) = 0 ∧
      runBudget bounds budget (.inl 1) = budget.create := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [runBudget, Fin.sum_univ_succ, laterCost, PqxdhDeploymentCompileBudget.cost, PqxdhDeploymentCompileBudget.unit,
      PqxdhDeploymentLaterCompile.runCap_create]

/-- The compiled scan of the run part meets the caps of the run part (`PqxdhRegistrationJointAcceptCut.scan_bound` through `PqxdhDeploymentIdealLaterCut.compile_scanSnap`). -/
theorem scan_certifiedL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects first) (index : ℕ)
    (kind : PqxdhRegistrationJointRevealCosts.SourceKind) :
    (PqxdhDeploymentIdealLaterCut.compileCutSnap setup codec route <$> (simulateQ (compileSnapImpl setup codec route)
        (scanCE (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first)) index)).run
          (Snap.empty, Local.empty)).IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = kind) (runBudget bounds budget kind) := by
  rw [← PqxdhDeploymentIdealLaterCut.compile_scanSnap]
  exact PqxdhRegistrationJointAcceptCut.scan_bound _ index _ _
    (run_certified setup codec route bounds mode first budget respects kind)

end Budget

/-! ### The reduction of the later second compile lemma -/

section Reduction
open PqxdhServerRootPreparation (Verified)
open PqxdhDeploymentBackend (XState handlerWith)
open PqxdhDeploymentIdealSteps (IdealBk TableState idealReg idealInit)
open PqxdhDeploymentIdealParams (Target Params drawParams)
open PqxdhDeploymentFinishErasure (laterWith laterTail realPost)
open PqxdhDeploymentInterface (Budget FreshBounds Mode ModeSpec asModeO)
open PqxdhDeploymentKemTransfer (Observed selectedKem)
open PqxdhDeploymentSecrecy (Ledger wrap)
open LazyOracleDiscard (LawEq)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {A Out : Type}

/-- The selected-key branch of the later second compile lemma at the challenger's draws `p` (an obligation of unit B; `selected_of_activeL` derives it from the active branch `ActiveBranchL`): for every constructed Server and every outcome of the common prefix (with the relation at the cut for the run part's budget) whose CE cut is pending at raw bytes that verify to the selected PQ key, item 2's side (`itemRestL`) and the CE side (`resumeL` with the later decision together with the mark) have the same law. -/
def SelectedBranchL (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (budget : Budget)
    (event : Observed Out → Bool) (claim : Observed Out → Option PqxdhDeploymentInterface.Handle)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) (p : Params KemSK budget.create) : Prop :=
  ∀ (born : Option (PqxdhLiveServerConstruction.Created Unit) × PqxdhRegistrationJointServerPrefix.State KemSK A),
    born ∈ support ((PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId none).run
      ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)) →
    ∀ created, born.1 = some created →
    ∀ reached, reached ∈ support (commonPrefixL setup codec route checks (Target.ofCE budget g) p created born.2.1
      (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first))) →
    PqxdhDeploymentIdealLaterCut.CutRelL setup codec route (Target.ofCE budget g) p created (runBudget bounds budget)
      reached →
    ∀ raw next, reached.1.1 = .pending raw next →
    ∀ value, PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value →
    value.keys.pqKey = p.chosen.1 →
    LawEq (itemRestL (Reader := Reader) setup codec route checks (Target.ofCE budget g) p
        (PqxdhDeploymentLaterServerTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        second (PqxdhRegistrationJointServerBirth.encode created) born.2.2 reached)
      (resumeL setup codec route checks (Target.ofCE budget g) p created
        (markedDecisionL setup codec budget event claim g) second born.2.2 reached.1.1
        (reached.1.2.1, (merge reached.1.2.2 (PqxdhRegistrationJointSchedule.source reached.2.1), reached.2.2)))

/-- The later second compile lemma from its selected-key branch: for a budget-respecting run-phase adversary, every post-run adversary and a CE designation `g`, if the selected-key branch holds at every draw of the challenger, item 2's logged two-slot world of the compiled LQ-F program accepts the per-target decision with the probability with which the later ideal game ends with the LQ-F event and the designation `g`. Everything else is proved here: the draws (`PqxdhDeploymentIdealLaterParams.laterSlotGame_pool`), the prefixes on both sides (`laterSlotGameAt_cut`, `PqxdhDeploymentIdealLaterCut.ideal_prefixL`), the key match (`game_markedL`), a failed construction, a completed cut and a cut whose raw bytes do not verify to the selected PQ key (`itemRestL_dead`, `resumeL_dead`), with the run part's budget (`scan_certifiedL`, `runBudget_caps`, `run_certified`). Premises: the approved codec contracts and the run-phase budget. -/
theorem ideal_compile_server_of_selected (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (event : Observed Out → Bool)
    (claim : Observed Out → Option PqxdhDeploymentInterface.Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A)
    (selected : ∀ p ∈ support (drawParams setup budget.create),
      SelectedBranchL (Reader := Reader) setup codec route checks ensureInit bounds mode first second budget event claim g
        runtime p) :
    𝒟[PqxdhDeploymentLaterServerItemTargets.laterSlotGame (Reader := Reader) setup codec checks ensureInit none
        (PqxdhDeploymentLaterServerTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (PqxdhDeploymentLaterServerCompile.compileServer setup codec route bounds mode first second) runtime
        budget.create (selectedKem budget g) g.1.val 2] {true} =
      𝒟[ceDecideL setup codec budget event claim g <$>
        (PqxdhDeploymentIdealLaterGame.idealLaterGame setup codec route checks budget g ensureInit bounds mode first
          second).run runtime] {true} := by
  obtain ⟨unreadIdentity, unreadKem, creates⟩ := runBudget_caps bounds budget
  have room : ∀ p : Params KemSK budget.create,
      runBudget bounds budget (.inl 1) ≤ (p.pool (Target.ofCE budget g)).length := by
    intro p
    rw [PqxdhDeploymentIdealParams.pool_length, creates]
    exact Nat.le_succ _
  have perDraw : ∀ p ∈ support (drawParams setup budget.create),
      LawEq (PqxdhDeploymentIdealLaterParams.laterSlotGameAt (Reader := Reader) setup codec checks ensureInit none
          (PqxdhDeploymentLaterServerTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
          (PqxdhDeploymentLaterServerCompile.compileServer setup codec route bounds mode first second) runtime
          budget.create (selectedKem budget g) g.1.val 2 p)
        (ceDecideL setup codec budget event claim g <$>
          (laterWith setup codec route idealInit (idealReg setup codec route checks (Target.ofCE budget g) p)
            (realPost setup codec checks) ensureInit 0 bounds mode first second).run runtime) := by
    intro p drawn
    rw [show selectedKem budget g = (Target.ofCE budget g).kem from rfl,
      show g.1.val = (Target.ofCE budget g).accept from rfl,
      laterSlotGameAt_cut setup codec route checks (Target.ofCE budget g) p _ ensureInit bounds mode first second
        runtime (runBudget bounds budget)
        (scan_certifiedL setup codec route bounds mode first budget respects _) unreadIdentity unreadKem (room p),
      game_markedL setup codec route checks phase1 budget event claim g p ensureInit bounds mode first second runtime,
      PqxdhDeploymentIdealLaterCut.ideal_prefixL setup codec route checks (Target.ofCE budget g) p phase1 phase2
        ensureInit bounds mode first second runtime]
    refine PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun born bornMember => ?_
    rcases born with ⟨_ | created, after⟩
    · exact LawEq.of_eq (by rw [itemPostL_failed]; simp [markedDecisionL])
    · dsimp only
      obtain ⟨installed, constructed⟩ := PqxdhRegistrationJointServerBirth.source_constructor setup.joint ensureInit
        setup.serverKeyId none _ after created bornMember
      obtain ⟨sender, peers⟩ := PqxdhDeploymentCompileGame.construct_fields setup.joint ensureInit _ setup.serverKeyId
        runtime created after.2 constructed
      have slot := PqxdhRegistrationJointServerBirth.source_owned setup.joint ensureInit setup.serverKeyId none _ after
        created bornMember
      have empty : after.1.2 = PqxdhLiveKemBirth.empty := by rw [installed]; rfl
      refine PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun reached reachedMember => ?_
      by_cases active : ∃ raw next value, reached.1.1 = .pending raw next ∧
          PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value ∧
          value.keys.pqKey = p.chosen.1
      · obtain ⟨raw, next, value, pending, verified, matched⟩ := active
        exact selected p drawn (some created, after) bornMember created rfl reached reachedMember
          (PqxdhDeploymentIdealLaterCut.cut_relL setup codec route checks (Target.ofCE budget g) p created phase1 phase2
            sender peers after.1 empty slot _ (runBudget bounds budget)
            (run_certified setup codec route bounds mode first budget respects) (room p) reached reachedMember)
          raw next pending value verified matched
      · have dead : ∀ raw next, reached.1.1 = .pending raw next → ∀ value,
            PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value →
              value.keys.pqKey ≠ p.chosen.1 :=
          fun raw next pending value verified matched => active ⟨raw, next, value, pending, verified, matched⟩
        exact (itemRestL_dead setup codec route checks (Target.ofCE budget g) p
          (PqxdhDeploymentLaterServerTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
          second (PqxdhRegistrationJointServerBirth.encode created) after.2 reached dead).trans
          (resumeL_dead setup codec route checks (Target.ofCE budget g) p created
            (fun outcome => decide (PqxdhDeploymentLaterServerTransfer.happens event outcome = true ∧
              PqxdhDeploymentLaterServerTransfer.designated setup.source.crypto codec setup.serverKeyId budget claim
                outcome = some g)) second after.2 reached.1.1 _ dead).symm
  have total := (PqxdhDeploymentSeedSplit.LawEq.bind_support (drawParams setup budget.create) perDraw).evalDist_eq
  have unfolded : (PqxdhDeploymentIdealLaterGame.idealLaterGame setup codec route checks budget g ensureInit bounds mode
      first second).run runtime = drawParams setup budget.create >>= fun p =>
        (laterWith setup codec route idealInit (idealReg setup codec route checks (Target.ofCE budget g) p)
          (realPost setup codec checks) ensureInit 0 bounds mode first second).run runtime := rfl
  rw [PqxdhDeploymentIdealLaterParams.laterSlotGame_pool, total, unfolded, map_bind]

/-- The active branch of the later second compile lemma at the challenger's draws `p` (the obligation of unit B2's post-challenge simulation): for every constructed Server, every outcome of the common prefix with the relation at the cut whose CE cut is pending at raw bytes that verify to the selected PQ key, and every outcome of the native steps before encapsulation that reaches the encapsulation with an ephemeral, item 2's logged post-challenge phase on the active cut and the CE side from the steps after encapsulation (`activeCEL`, with the later decision together with the mark) have the same law. -/
def ActiveBranchL (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (budget : Budget)
    (event : Observed Out → Bool) (claim : Observed Out → Option PqxdhDeploymentInterface.Handle)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) (p : Params KemSK budget.create) : Prop :=
  ∀ (born : Option (PqxdhLiveServerConstruction.Created Unit) × PqxdhRegistrationJointServerPrefix.State KemSK A),
    born ∈ support ((PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId none).run
      ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)) →
    ∀ created, born.1 = some created →
    ∀ reached, reached ∈ support (commonPrefixL setup codec route checks (Target.ofCE budget g) p created born.2.1
      (wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first))) →
    PqxdhDeploymentIdealLaterCut.CutRelL setup codec route (Target.ofCE budget g) p created (runBudget bounds budget)
      reached →
    ∀ raw next, reached.1.1 = .pending raw next →
    ∀ value, PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value →
    value.keys.pqKey = p.chosen.1 →
    ∀ pre, pre ∈ support ((simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup codec checks created.seed)
      (PqxdhDeploymentLaterServerSource.beforeLogged (Shared := PqxdhBeaconPhase2Preparation.Word32) value)).run
        reached.2.1.shared.2.server.consumed) →
    ∀ ephemeral, pre.1.1 = some ephemeral →
    LawEq (itemPostL (Reader := Reader) setup codec checks (Target.ofCE budget g) p
        (PqxdhDeploymentLaterServerTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (.ready (PqxdhRegistrationJointServerBirth.encode created) p.others
          (some (.pending raw value ephemeral pre.2 reached.2.1.shared
            (PqxdhRegistrationJointGeneratedFinish.encodeState setup reached.2.1).owners reached.2.2
            (compiledNextL setup codec route second raw next reached.1.2)))
          (reached.2.1.pool.1, PqxdhDeploymentIdealPoolSource.routerOf reached.2.1.pool.2) born.2.2))
      (activeCEL setup codec route checks (Target.ofCE budget g) p created
        (markedDecisionL setup codec budget event claim g) second born.2.2
        (reached.1.2.1, (merge reached.1.2.2 (PqxdhRegistrationJointSchedule.source reached.2.1), reached.2.2)) next
        value ephemeral pre.2 pre.1.2)

/-- The selected-key branch from the active branch: on both sides the native steps before encapsulation of the Server's seed come first (`itemRestL_selected`, `resumeL_selected`), a rejection before encapsulation accepts nothing on both sides, and an ephemeral leads to the active branch. -/
theorem selected_of_activeL (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (budget : Budget)
    (event : Observed Out → Bool) (claim : Observed Out → Option PqxdhDeploymentInterface.Handle)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) (p : Params KemSK budget.create)
    (active : ActiveBranchL (Reader := Reader) setup codec route checks ensureInit bounds mode first second budget event
      claim g runtime p) :
    SelectedBranchL (Reader := Reader) setup codec route checks ensureInit bounds mode first second budget event claim g
      runtime p := by
  intro born bornMember created constructed reached reachedMember related raw next pending value verified matched
  rw [pending]
  refine (itemRestL_selected setup codec route checks (Target.ofCE budget g) p _ second _ born.2.2 reached raw next
    pending value verified created.seed).trans (LawEq.trans ?_ (resumeL_selected setup codec route checks
      (Target.ofCE budget g) p created
      (fun outcome => decide (PqxdhDeploymentLaterServerTransfer.happens event outcome = true ∧
        PqxdhDeploymentLaterServerTransfer.designated setup.source.crypto codec setup.serverKeyId budget claim outcome =
          some g)) second born.2.2
      (reached.1.2.1, (merge reached.1.2.2 (PqxdhRegistrationJointSchedule.source reached.2.1), reached.2.2)) raw next
      value verified matched).symm)
  refine PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun pre preMember => ?_
  rcases found : pre.1.1 with _ | ephemeral
  · exact LawEq.refl _
  · exact active born bornMember created constructed reached reachedMember related raw next pending value verified matched
      pre preMember ephemeral found

/-- The later second compile lemma from its active branch: `ideal_compile_server_of_selected` with `selected_of_activeL`. Premises: the approved codec contracts, the run-phase budget and the active branch at every draw of the challenger. -/
theorem ideal_compile_server_of_active (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (budget : Budget)
    (respects : budget.Respects first) (event : Observed Out → Bool)
    (claim : Observed Out → Option PqxdhDeploymentInterface.Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A)
    (active : ∀ p ∈ support (drawParams setup budget.create),
      ActiveBranchL (Reader := Reader) setup codec route checks ensureInit bounds mode first second budget event claim g
        runtime p) :
    𝒟[PqxdhDeploymentLaterServerItemTargets.laterSlotGame (Reader := Reader) setup codec checks ensureInit none
        (PqxdhDeploymentLaterServerTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (PqxdhDeploymentLaterServerCompile.compileServer setup codec route bounds mode first second) runtime
        budget.create (selectedKem budget g) g.1.val 2] {true} =
      𝒟[ceDecideL setup codec budget event claim g <$>
        (PqxdhDeploymentIdealLaterGame.idealLaterGame setup codec route checks budget g ensureInit bounds mode first
          second).run runtime] {true} :=
  ideal_compile_server_of_selected setup codec route checks phase1 phase2 ensureInit bounds mode first second budget
    respects event claim g runtime fun p drawn =>
      selected_of_activeL setup codec route checks ensureInit bounds mode first second budget event claim g runtime p
        (active p drawn)

end Reduction

end BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.keymatch_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.keymatch_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.game_markedL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.game_markedL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.laterSlotGameAt_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.laterSlotGameAt_cut

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.itemPostL_failed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.itemPostL_failed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.itemPostL_dead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.itemPostL_dead

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.rejectRunL_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.rejectRunL_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.run_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.run_map

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.opaqueAfterL_dead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.opaqueAfterL_dead

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.itemRestL_dead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.itemRestL_dead

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.laterTail_marks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.laterTail_marks

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.resumeL_dead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.resumeL_dead

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.opaqueAfterL_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.opaqueAfterL_selected

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.itemRestL_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.itemRestL_selected

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.acceptStep_selectedL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.acceptStep_selectedL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.resumeL_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.resumeL_selected

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.run_certified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.run_certified

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.runBudget_caps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.runBudget_caps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.scan_certifiedL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.scan_certifiedL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.ideal_compile_server_of_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.ideal_compile_server_of_selected

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.selected_of_activeL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.selected_of_activeL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.ideal_compile_server_of_active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterBranch.ideal_compile_server_of_active

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch

/-!
# The branches of the second compile lemma at the cut (CE-11b, unit U6)

The second compile lemma of CE-11b (design-v2 section 8.1, `ideal_compile`) states that item 2's two-slot ideal world of the compiled CE program accepts the per-target decision with the probability with which `CE.idealGame g` ends with the event and the claim designating `g`. Unit U5 cut both sides at the selected raw accept (`PqxdhDeploymentIdealCut`); this module splits the comparison at the cut into its branches, proves every branch except the one where the selected accept's raw bytes verify to the selected PQ key, and reduces `ideal_compile` to that branch (`ideal_compile_of_selected`, from the obligation `SelectedBranch`).

- The CE decision reads the mark. With the key match (`PqxdhDeploymentIdealKeymatch.target_marked`), on every outcome of the experiment with the ideal registration where the event happens and the claim designates `g`, the selected session is marked, so the CE decision (`ceDecide`) equals the decision together with the mark (`markedDecision`, `game_marked`). `ideal_cutMarked` and `ideal_prefixMarked` are `PqxdhDeploymentIdealCut.ideal_cut` and `ideal_prefix` for a decision that also reads the mark (`marked`, `resumeMarked`): before the cut no session is marked.
- Item 2's side at the cut. `slotGameAt_cut`: item 2's two-slot ideal world at the challenger's draws is the Server construction, then the common prefix (`PqxdhDeploymentIdealCut.commonPrefix`) and `itemRest`: the rest of item 2's opaque scan under the stopped router, then item 2's post-challenge phase (`itemPost`, the services skeleton with the factored services under item 2's public-table layer and the first-touch allocator in front of the two-slot table).
- The branches without an active cut accept nothing on both sides: a failed construction (`itemPost_failed`), a completed cut, and a pending cut whose raw bytes do not verify to the selected PQ key (`itemRest_dead`, through `opaqueRest_dead`, `rejectRun_complete` and `optionRun_support`; `resumeMarked_dead`, through `PqxdhDeploymentIdealKeymatch.handler_accept_inactive` and `run_settled`: the selected accept is then the logged accept and leaves no mark).
- The CE budget at the cut: CE-9's transported caps bound item 2's scan of the compiled program (`scan_certified`), read no identity or KEM field (`transported_unread`) and fit the pool (`transported_pool`).
- `CutRelIndexed` strengthens the relation at the cut (`PqxdhDeploymentIdealCut.CutRel`, whose module is published) by the owner positions (owner `j`'s active KEM key pair is pool entry `j`) and the remaining creations of the continuation; `cut_relIndexed` proves it on every outcome of the common prefix from a source budget of the whole compiled program.
- `ideal_compile_of_selected`: under the approved codec contracts and the budget, `ideal_compile` holds once `SelectedBranch` holds at every draw of the challenger. `SelectedBranch` is the selected-key branch: for every outcome of the common prefix with `CutRelIndexed` whose cut is pending at raw bytes that verify to the selected PQ key, `itemRest` and `resumeMarked` with the decision together with the mark have the same law. It is the remaining part of unit U6 (the steps before encapsulation, the post-challenge simulation and the decision step); this module does not prove it.

Premises: the approved codec contracts `Phase1ReadBack` and `Phase2ReadBack` and the CE budget. These are program equalities, equalities in law and support facts. They charge nothing and make no security claim; `ideal_compile_of_selected` is a reduction, not the second compile lemma.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentCompile (Local merge compileImpl)
open PqxdhDeploymentIdealCut (CutCE scanCE finishCE cutState unghost commonPrefix)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X : Type}

/-! ### The cut with a decision that reads the mark -/

section Marked
open PqxdhDeploymentBackend (XState RegImpl handlerWith xinitial gameWith)
open PqxdhDeploymentIdealSteps (IdealCore IdealBk TableState idealReg idealInit)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealPool (deploymentPool)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- Whether the selected session is marked in an extended state. -/
def marked (x : XState KemSK (IdealBk TableState) 2) : Bool := x.backend.2.2.marks.isSome

/-- The ideal game after the cut, for a decision that reads the result, the deployment state and whether the selected session is marked: from the canonical state at the cut, resume the cut with the ideal registration. -/
noncomputable def resumeMarked {Y : Type} (decision : Y × PqxdhDeploymentNative.State KemSK × Bool → Bool)
    (cut : CutCE Y) (base : PqxdhDeploymentNative.State KemSK) : ProbComp Bool :=
  (fun outcome => decision (outcome.1, outcome.2.base, marked outcome.2)) <$>
    (simulateQ (handlerWith setup codec route (idealReg setup codec route checks t p created)) (finishCE cut)).run
      (cutState t created base)

/-- `PqxdhDeploymentIdealCut.ideal_cut` for a decision that also reads whether the selected session is marked: the run from the initial state is the pool scan followed by `resumeMarked`. Before the cut no session is marked, and the canonical state at the cut marks none. -/
theorem ideal_cutMarked {Y : Type} (decision : Y × PqxdhDeploymentNative.State KemSK × Bool → Bool)
    (work : OracleComp Spec Y) :
    (fun outcome => decision (outcome.1, outcome.2.base, marked outcome.2)) <$>
        (simulateQ (handlerWith setup codec route (idealReg setup codec route checks t p created)) work).run
          (xinitial created (idealInit created)) =
      (simulateQ (deploymentPool setup codec checks route created.seed (p.pool t)) (scanCE work t.accept)).run
          (PqxdhDeploymentNative.initial created) >>= fun reached =>
        resumeMarked setup codec route checks t p created decision reached.1 reached.2 := by
  have pre : PqxdhDeploymentIdealCut.PreCut (xinitial (KemSK := KemSK) (n := 2) created (idealInit created)) :=
    ⟨rfl, rfl⟩
  have scanned := PqxdhDeploymentIdealCut.preScan setup codec route checks t p created work t.accept _ pre
    (by simp [xinitial, idealInit, PqxdhDeploymentIdealSteps.IdealCore.initial])
  rw [PqxdhDeploymentIdealCut.run_scanCE _ work t.accept, map_bind]
  rw [show PqxdhDeploymentNative.initial created =
    (xinitial (KemSK := KemSK) (n := 2) created (idealInit created)).base from rfl, ← scanned.1, bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun reached member => ?_
  obtain ⟨accepts, backend, seeds, pending⟩ := scanned.2 reached member
  have reads : ∀ (state : XState KemSK (IdealBk TableState) 2),
      (fun outcome : Y × XState KemSK (IdealBk TableState) 2 =>
          decision (outcome.1, outcome.2.base, marked outcome.2)) <$>
          (simulateQ (handlerWith setup codec route (idealReg setup codec route checks t p created))
            (finishCE reached.1)).run state =
        (fun outcome : Y × XState KemSK (IdealBk TableState) 2 =>
          decision (outcome.1, outcome.2.base, marked outcome.2)) <$>
          (simulateQ (handlerWith setup codec route (idealReg setup codec route checks t p created))
            (finishCE reached.1)).run (unghost state) := by
    intro state
    have ghost := congrArg (fun work => (fun outcome : Y × XState KemSK (IdealBk TableState) 2 =>
      decision (outcome.1, outcome.2.base, marked outcome.2)) <$> work)
      (PqxdhDeploymentIdealCut.idealRun_unghost setup codec route checks t p created (finishCE reached.1) state)
    rw [Functor.map_map, Functor.map_map] at ghost
    exact ghost
  change _ = resumeMarked setup codec route checks t p created decision reached.1 reached.2.base
  rw [reads]
  unfold resumeMarked
  rcases cut : reached.1 with result | ⟨raw, next⟩
  · simp only [finishCE, simulateQ_pure, StateT.run_pure, map_pure]
    change pure (decision (result, reached.2.base, reached.2.backend.2.2.marks.isSome)) = _
    rw [backend]
    rfl
  · have counted := pending raw next cut
    have same : unghost reached.2 = cutState t created reached.2.base := by
      have : reached.2 = ⟨reached.2.base, reached.2.backend, reached.2.seeds, reached.2.snap, reached.2.log⟩ := rfl
      rw [this]
      simp only [unghost, cutState, backend, seeds, counted]
      simp [xinitial, idealInit, PqxdhDeploymentIdealSteps.IdealCore.initial]
    rw [same]

/-- `PqxdhDeploymentIdealCut.ideal_prefix` for a decision that also reads whether the selected session is marked: the common deployment experiment with the ideal registration at the draws is the Server construction, then the common prefix, then `resumeMarked` on the merged deployment state. Premises: the approved codec contracts. -/
theorem ideal_prefixMarked {A : Type} (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (ensureInit : StateT A ProbComp Bool)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (runtime : A)
    (decision : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × (X × PqxdhDeploymentSecrecy.Ledger) ×
      PqxdhDeploymentNative.State KemSK × Bool) → Bool) :
    (fun outcome => decision (outcome.1.map fun result =>
        (result.1, (result.2.1, result.2.2.1), result.2.2.2.base, marked result.2.2.2))) <$>
        (gameWith setup codec route idealInit (idealReg setup codec route checks t p) ensureInit 0 bounds mode
          adversary).run runtime =
      (PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId none).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) >>= fun born =>
        match born.1 with
        | none => pure (decision none)
        | some created =>
            commonPrefix setup codec route checks t p created born.2.1
                (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds
                  (PqxdhDeploymentInterface.asModeO mode adversary))
              >>= fun reached =>
              resumeMarked setup codec route checks t p created
                (fun outcome => decision (some (PqxdhRegistrationJointServerBirth.encode created, outcome.1, outcome.2.1,
                  outcome.2.2)))
                reached.1.1 (merge reached.1.2 (PqxdhRegistrationJointSchedule.source reached.2)) := by
  simp only [gameWith, PqxdhRegistrationJointServerBirth.source, StateT.run, map_bind, bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun born member => ?_
  rcases born with ⟨_ | created, after⟩
  · simp
  · obtain ⟨sender, peers⟩ := PqxdhDeploymentCompileGame.construct_fields setup.joint ensureInit 0 setup.serverKeyId
      runtime created after member
    dsimp only
    have cut := ideal_cutMarked setup codec route checks t p created
      (fun outcome => decision (some (PqxdhRegistrationJointServerBirth.encode created, outcome.1, outcome.2.1,
        outcome.2.2)))
      (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds
        (PqxdhDeploymentInterface.asModeO mode adversary))
    rw [PqxdhDeploymentIdealCut.pool_scan_source setup codec route checks t p created phase1 phase2 sender peers
      created.server.server.metadata.identityIndex
      (PqxdhRegistrationJointServerBirth.install created (PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty)),
      bind_map_left] at cut
    rw [Functor.map_map]
    exact cut

end Marked

/-! ### The CE decision reads the mark -/

section Decision
open PqxdhDeploymentBackend (XState gameWith)
open PqxdhDeploymentIdealSteps (IdealBk TableState idealReg idealInit)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentKemTransfer (Observed happens designated target)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks)

/-- The classical view of an outcome of the common deployment experiment with a registration backend: the constructed Server's public data, the adversary's output, the ledger and the deployment state. -/
def classicalOf {A Bk : Type} {n : ℕ} (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X ×
    PqxdhDeploymentSecrecy.Ledger × XState KemSK Bk n) × A) :
    Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A :=
  (outcome.1.map fun result => (result.1, result.2.1, (result.2.2.1, result.2.2.2.base)), outcome.2)

/-- The CE decision of the second compile lemma on an outcome: the event happens and the claim designates `g`. -/
noncomputable def ceDecide {A Bk : Type} {n : ℕ} (budget : PqxdhDeploymentInterface.Budget) (event : Observed X → Bool)
    (claim : Observed X → Option PqxdhDeploymentInterface.Handle) (g : Fin budget.accept × Fin budget.capacity)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.Ledger ×
      XState KemSK Bk n) × A) : Bool :=
  decide (happens event (classicalOf outcome) = true ∧
    designated setup.source.crypto codec setup.serverKeyId budget claim (classicalOf outcome) = some g)

/-- The CE decision together with the mark, on the classical view with the mark: the event happens on the observation, the claim designates `g`, and the selected session is marked. -/
noncomputable def markedDecision (budget : PqxdhDeploymentInterface.Budget) (event : Observed X → Bool)
    (claim : Observed X → Option PqxdhDeploymentInterface.Handle) (g : Fin budget.accept × Fin budget.capacity) :
    Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × (X × PqxdhDeploymentSecrecy.Ledger) ×
      PqxdhDeploymentNative.State KemSK × Bool) → Bool
  | none => false
  | some outcome =>
      decide (event (outcome.2.1.1, outcome.2.1.2, outcome.2.2.1.produced) = true ∧
        target setup.source.crypto codec setup.serverKeyId budget claim
          (outcome.2.1.1, outcome.2.1.2, outcome.2.2.1.produced) = some g) && outcome.2.2.2

/-- With the key match (`PqxdhDeploymentIdealKeymatch.target_marked`), the CE decision on the experiment with the ideal registration at the target of `g` is the decision together with the mark: on every outcome where the event happens and the claim designates `g`, the selected session is marked. Premise: `Phase1ReadBack`. -/
theorem game_marked {A : Type} (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (budget : PqxdhDeploymentInterface.Budget) (event : Observed X → Bool)
    (claim : Observed X → Option PqxdhDeploymentInterface.Handle) (g : Fin budget.accept × Fin budget.capacity)
    (p : Params KemSK budget.create) (ensureInit : StateT A ProbComp Bool) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (runtime : A) :
    ceDecide setup codec budget event claim g <$>
        (gameWith setup codec route idealInit (idealReg setup codec route checks (Target.ofCE budget g) p) ensureInit 0
          bounds mode adversary).run runtime =
      (fun outcome => markedDecision setup codec budget event claim g (outcome.1.map fun result =>
        (result.1, (result.2.1, result.2.2.1), result.2.2.2.base, marked result.2.2.2))) <$>
        (gameWith setup codec route idealInit (idealReg setup codec route checks (Target.ofCE budget g) p) ensureInit 0
          bounds mode adversary).run runtime := by
  apply PqxdhDeploymentKemTransfer.map_support_congr
  rintro ⟨_ | ⟨created, output, ledger, final⟩, after⟩ member
  · simp [ceDecide, classicalOf, markedDecision, happens, designated, PqxdhDeploymentKemTransfer.observeGame]
  · simp only [ceDecide, classicalOf, markedDecision, happens, designated, PqxdhDeploymentKemTransfer.observeGame,
      Option.map_some, Option.any_some, Option.bind_some]
    by_cases chosen : target setup.source.crypto codec setup.serverKeyId budget claim (output, ledger, final.base.produced) =
      some g
    · have mark := PqxdhDeploymentIdealKeymatch.target_marked setup codec route checks phase1 budget g p ensureInit 0 bounds
        mode adversary runtime _ member created output ledger final rfl claim chosen
      simp only [marked, mark, Bool.and_true]
      exact decide_eq_decide.mpr Iff.rfl
    · simp [chosen]

end Decision

/-! ### Item 2's side at the cut -/

section Item2
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhRegistrationJointKemEntryFactor (Output factoredServices publicLocalV)
open PqxdhRegistrationJointKemRawOpaque (OpaqueContext)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count) {A Y : Type}
  (decision : Y × Local → Bool)

/-- Item 2's post-challenge phase at the challenger's draws, from a prechallenge context: the services skeleton's post-challenge phase with the factored services under item 2's public-table layer, from the table cache held by the context, then the first-touch allocator in front of item 2's two-slot table. -/
noncomputable def itemPost (context : OpaqueContext Reader KemSK A (Y × Local) count) : ProbComp Bool :=
  (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl (D := PqxdhCorrelatedExtractFamily.Message)
      (PqxdhRegistrationJointKemSecondEntry.tableService (n := 2)))
    ((simulateQ (publicLocalV Output) (PqxdhRegistrationJointKemPostSkeleton.postSkel setup codec checks decision count
      t.kem (factoredServices setup codec checks) p.chosen p.challenge context)).run'
        (PqxdhRegistrationJointKemPostSkeleton.cacheOf context))).run'
    (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial)

/-- Item 2's side after the common prefix: the rest of item 2's opaque scan (`PqxdhDeploymentIdealCut.opaqueRest`) under the stopped selected-first router at the pool, from the compiled cut with the encoded owners and the native state, then the post-challenge phase on the resulting prechallenge context. -/
noncomputable def itemRest (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (after : A)
    (reached : (CutCE Y × Local) × PqxdhRegistrationJointSchedule.State KemSK) : ProbComp Bool :=
  ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem t.kem.val (p.pool t))
      (PqxdhDeploymentIdealCut.opaqueRest setup codec checks created.server.server.metadata.identityIndex
        created.publicIdentity (PqxdhRegistrationJointAcceptCutTag.decideTag decision)
        ((PqxdhDeploymentIdealCut.compileCut setup codec route reached.1,
          (PqxdhRegistrationJointGeneratedFinish.encodeState setup reached.2).owners), reached.2.shared))).run).run
      (reached.2.pool.1, PqxdhDeploymentIdealPoolSource.routerOf reached.2.pool.2) >>= fun result =>
    itemPost setup codec checks t p decision (.ready created p.others result.1 result.2 after)

/-- Item 2's two-slot ideal world at the challenger's draws (`PqxdhDeploymentIdealParams.slotGameAt`), for the compiled program of a deployment program, is the Server construction, then on a constructed Server the common prefix (`commonPrefix`) and `itemRest`, and on a failed construction the post-challenge phase of the failed context. Premises: a source budget for item 2's scan of the compiled program that reads no identity or KEM field and creates no more KEM keys than the pool holds (those of `PqxdhDeploymentIdealCut.item2_prefix`). -/
theorem slotGameAt_cut (ensureInit : StateT A ProbComp Bool) (work : OracleComp Spec Y) (runtime : A)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → ℕ)
    (certified : ∀ source, (PqxdhRegistrationJointAcceptCut.scan (PqxdhDeploymentCompile.compile setup codec route work)
      t.accept).IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (unreadIdentity : budget (.inr 0) = 0) (unreadKem : budget (.inr 1) = 0)
    (room : budget (.inl 1) ≤ (p.pool t).length) :
    PqxdhDeploymentIdealParams.slotGameAt (Reader := Reader) setup codec checks ensureInit none decision
        (PqxdhDeploymentCompile.compile setup codec route work) runtime count t.kem t.accept 2 p =
      (PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId none).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) >>= fun born =>
        match born.1 with
        | none => itemPost setup codec checks t p decision (.failed born.2)
        | some created =>
            commonPrefix setup codec route checks t p created born.2.1 work >>= fun reached =>
              itemRest setup codec route checks t p decision (PqxdhRegistrationJointServerBirth.encode created) born.2.2
                reached := by
  unfold PqxdhDeploymentIdealParams.slotGameAt PqxdhDeploymentIdealParams.entryClientAt
  rw [PqxdhDeploymentIdealParams.internalize_run]
  unfold PqxdhDeploymentIdealParams.startPool
  rw [bind_assoc]
  simp only [pure_bind]
  rw [PqxdhDeploymentIdealCut.item2_prefix setup codec route checks t p ensureInit decision work runtime budget certified
    unreadIdentity unreadKem room, bind_assoc]
  refine bind_congr fun born => ?_
  rcases born with ⟨_ | created, after⟩
  · simp only [pure_bind]
    rfl
  · simp only [bind_assoc, pure_bind]
    rfl

/-- On a failed construction, item 2's post-challenge phase accepts nothing. -/
theorem itemPost_failed (state : PqxdhRegistrationJointServerPrefix.State KemSK A) :
    itemPost setup codec checks t p decision (.failed state) = pure false := by
  simp only [itemPost, PqxdhRegistrationJointKemPostSkeleton.postSkel, simulateQ_pure, StateT.run'_eq, StateT.run_pure,
    map_pure]

/-- Item 2's post-challenge phase accepts nothing on a prechallenge context without an active cut at the selected PQ key: a stopped run, a completed run, or a cut whose verified PQ key is not the selected one. -/
theorem itemPost_dead (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit)
    (cut : Option (PqxdhRegistrationJointKemRawOpaque.OpaqueCut Reader KemSK (Y × Local) Bool))
    (state : PqxdhDynamicKemJointSource.State KemSK) (after : A)
    (dead : ∀ raw value ephemeral consumed native owners next,
      cut = some (.pending raw value ephemeral consumed native owners next) → value.keys.pqKey ≠ p.chosen.1) :
    itemPost setup codec checks t p decision (.ready created p.others cut state after) = pure false := by
  rcases cut with _ | (outcome | ⟨raw, value, ephemeral, consumed, native, owners, next⟩)
  · simp only [itemPost, PqxdhRegistrationJointKemPostSkeleton.postSkel, simulateQ_pure, StateT.run'_eq, StateT.run_pure,
      map_pure]
  · simp only [itemPost, PqxdhRegistrationJointKemPostSkeleton.postSkel, simulateQ_pure, StateT.run'_eq, StateT.run_pure,
      map_pure]
  · have other := dead raw value ephemeral consumed native owners next rfl
    simp only [itemPost, PqxdhRegistrationJointKemPostSkeleton.postSkel, other, ↓reduceIte, simulateQ_pure,
      StateT.run'_eq, StateT.run_pure, map_pure]

end Item2

/-! ### Results of a run through an optional stateful interpreter -/

section Option

/-- A value returned by a run through an interpreter into `OptionT (StateT σ ProbComp)` is a value of the program. -/
theorem optionRun_support {ι' σ α : Type} {spec' : OracleSpec ι'} (impl : QueryImpl spec' (OptionT (StateT σ ProbComp)))
    (work : OracleComp spec' α) (state : σ) (result : Option α × σ)
    (member : result ∈ support ((simulateQ impl work).run.run state)) :
    ∀ value, result.1 = some value → value ∈ support work := by
  induction work using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      intro found same
      simp only [Option.some.injEq] at same
      subst same
      simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        OptionT.run_bind, Option.elimM, StateT.run_bind, mem_support_bind_iff] at member
      obtain ⟨answer, -, member⟩ := member
      rcases answer with ⟨_ | reply, after⟩
      · simp only [Option.elim, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
        subst member
        intro found same
        cases same
      · intro found same
        have inner := ih reply after result member found same
        simp only [support_bind, Set.mem_iUnion, exists_prop]
        exact ⟨reply, by simp, inner⟩

end Option

/-! ### The branches without an active cut -/

section Dead
open PqxdhDeploymentBackend (XState handlerWith)
open PqxdhDeploymentIdealSteps (IdealBk TableState idealReg idealInit)
open PqxdhDeploymentIdealParams (Target Params)
open LazyOracleDiscard (LawEq)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count) {A Y : Type}

/-- The completion of a raw accept by `rejectRun` is never a pending cut. -/
theorem rejectRun_complete {Z R : Type} (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (observe : Z × PqxdhRegistrationJointAcceptCutTag.Tag → R) (raw : Pqxdh.Bytes)
    (next : Option ℕ → OracleComp (PqxdhRegistrationJointKemCommands.SourceSpec KemSK) Z)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (state : PqxdhServerAuthNative.NativeState KemSK)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes)
    (cut : PqxdhRegistrationJointKemRawOpaque.OpaqueCut Reader KemSK Z R)
    (member : cut ∈ support (PqxdhRegistrationJointKemRawOpaque.rejectRun setup codec checks identityIndex publicIdentity
      observe raw next owners state collected)) :
    ∃ outcome, cut = .complete outcome := by
  unfold PqxdhRegistrationJointKemRawOpaque.rejectRun at member
  rw [mem_support_bind_iff] at member
  obtain ⟨_, -, member⟩ := member
  rw [support_map] at member
  obtain ⟨outcome, -, rfl⟩ := member
  exact ⟨outcome, rfl⟩

/-- The rest of item 2's opaque scan has an active cut at the selected PQ key only from a pending compiled cut whose raw bytes verify to that key: if the CE cut is complete, or its raw bytes do not verify to the selected PQ key, no result of the rest is a pending cut with the selected PQ key. -/
theorem opaqueRest_dead {R : Type} (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (observe : (Y × Local) × PqxdhRegistrationJointAcceptCutTag.Tag → R) (cutCE : CutCE Y) (copies : Local)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry)
    (state : PqxdhServerAuthNative.NativeState KemSK)
    (dead : ∀ raw next, cutCE = .pending raw next → ∀ value,
      PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value → value.keys.pqKey ≠ p.chosen.1)
    (cut : PqxdhRegistrationJointKemRawOpaque.OpaqueCut Reader KemSK (Y × Local) R)
    (member : cut ∈ support (PqxdhDeploymentIdealCut.opaqueRest setup codec checks identityIndex publicIdentity observe
      ((PqxdhDeploymentIdealCut.compileCut setup codec route (cutCE, copies), owners), state))) :
    ∀ raw value ephemeral consumed native owners' next,
      cut = .pending raw value ephemeral consumed native owners' next → value.keys.pqKey ≠ p.chosen.1 := by
  intro raw value ephemeral consumed native owners' next same
  subst same
  rcases cutCE with result | ⟨raw0, next0⟩
  · simp [PqxdhDeploymentIdealCut.opaqueRest, PqxdhDeploymentIdealCut.compileCut] at member
  · unfold PqxdhDeploymentIdealCut.opaqueRest at member
    simp only [PqxdhDeploymentIdealCut.compileCut] at member
    rcases found : PqxdhRegistrationJointRawSignatures.verified setup codec checks raw0 with _ | verified
    · rw [found] at member
      obtain ⟨outcome, impossible⟩ := rejectRun_complete setup codec checks _ _ _ _ _ _ _ _ _ member
      cases impossible
    · rw [found] at member
      simp only [mem_support_bind_iff] at member
      obtain ⟨prepared, -, member⟩ := member
      split at member
      · obtain ⟨outcome, impossible⟩ := rejectRun_complete setup codec checks _ _ _ _ _ _ _ _ _ member
        cases impossible
      · rw [support_pure, Set.mem_singleton_iff] at member
        injection member with sameRaw sameValue
        subst sameValue
        exact dead raw0 next0 rfl _ found

/-- Item 2's side accepts with probability zero (in law, it is `pure false`) when the CE cut is complete or its raw bytes do not verify to the selected PQ key. -/
theorem itemRest_dead (decision : Y × Local → Bool) (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit)
    (after : A) (reached : (CutCE Y × Local) × PqxdhRegistrationJointSchedule.State KemSK)
    (dead : ∀ raw next, reached.1.1 = .pending raw next → ∀ value,
      PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value → value.keys.pqKey ≠ p.chosen.1) :
    LawEq (itemRest (Reader := Reader) setup codec route checks t p decision created after reached) (pure false) := by
  unfold itemRest
  refine (PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun result member => LawEq.of_eq
    (itemPost_dead setup codec checks t p decision created result.1 result.2 after ?_)).trans
    (LazyOracleDiscard.lawEq_drop _ _)
  intro raw value ephemeral consumed native owners next found
  have produced := optionRun_support _ _ _ result member _ found
  exact opaqueRest_dead setup codec route checks p _ _ _ reached.1.1 reached.1.2 _ _ dead _ produced raw value ephemeral
    consumed native owners next rfl

/-- A map that is constant on the support of a run has the law of `pure` of that constant. -/
theorem map_const_lawEq {α : Type} (run : ProbComp α) (decide : α → Bool) (value : Bool)
    (constant : ∀ outcome ∈ support run, decide outcome = value) : LawEq (decide <$> run) (pure value) := by
  rw [PqxdhDeploymentKemTransfer.map_support_congr run decide (fun _ => value) constant, map_eq_bind_pure_comp]
  exact LazyOracleDiscard.lawEq_drop _ _

/-- The CE side accepts with probability zero (in law, it is `pure false`) when the cut is complete or its raw bytes do not verify to the selected PQ key: the canonical state at the cut marks no session, the selected accept is then the logged accept and leaves no mark, and after it no run changes the mark (`PqxdhDeploymentIdealKeymatch.handler_accept_inactive`, `run_settled`). -/
theorem resumeMarked_dead (created : PqxdhLiveServerConstruction.Created Unit)
    (decision : Y × PqxdhDeploymentNative.State KemSK → Bool) (cut : CutCE Y) (base : PqxdhDeploymentNative.State KemSK)
    (dead : ∀ raw next, cut = .pending raw next → ∀ value,
      PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value → value.keys.pqKey ≠ p.chosen.1) :
    LawEq (resumeMarked setup codec route checks t p created (fun outcome => decision (outcome.1, outcome.2.1) &&
      outcome.2.2) cut base) (pure false) := by
  unfold resumeMarked
  apply map_const_lawEq
  intro outcome member
  suffices unmarked : marked outcome.2 = false by
    simp only [unmarked, Bool.and_false]
  rcases cut with result | ⟨raw, next⟩
  · simp only [finishCE, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    rfl
  · simp only [finishCE, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at member
    obtain ⟨accepted, acceptedMember, member⟩ := member
    obtain ⟨accepts, marks⟩ := PqxdhDeploymentIdealKeymatch.handler_accept_inactive setup codec route checks t p created
      raw (dead raw next rfl) (cutState t created base) rfl accepted acceptedMember
    have settled := PqxdhDeploymentIdealKeymatch.run_settled setup codec route checks t p created (next accepted.1)
      accepted.2 (by rw [accepts]; exact Nat.lt_succ_self _) outcome member
    simp only [marked, settled, marks, Option.isSome_none]

end Dead

/-! ### The CE budget at the cut -/

section Budget
open PqxdhDeploymentInterface (Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentCompileCaps (transported)

/-- The source budget of item 2's scan of the compiled program, from the CE budget: CE-9's transported caps (`PqxdhDeploymentCompileCaps.compile_full_certified` through `PqxdhRegistrationJointAcceptCut.scan_bound`). -/
theorem scan_certified (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary) (index : ℕ)
    (kind : PqxdhRegistrationJointRevealCosts.SourceKind) :
    (PqxdhRegistrationJointAcceptCut.scan (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)
        index).IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = kind)
      (transported bounds budget kind) :=
  PqxdhRegistrationJointAcceptCut.scan_bound _ index _ _
    (PqxdhDeploymentCompileCaps.compile_full_certified setup codec route bounds mode adversary budget respects kind)

/-- The transported caps read no identity or KEM field. -/
theorem transported_unread (bounds : FreshBounds) (budget : Budget) :
    transported bounds budget (.inr 0) = 0 ∧ transported bounds budget (.inr 1) = 0 := ⟨rfl, rfl⟩

/-- The transported creation cap fits the pool of a target of the CE budget. -/
theorem transported_pool (bounds : FreshBounds) (budget : Budget)
    (t : PqxdhDeploymentIdealParams.Target budget.create) (p : PqxdhDeploymentIdealParams.Params KemSK budget.create) :
    transported bounds budget (.inl 1) ≤ (p.pool t).length := by
  rw [PqxdhDeploymentIdealParams.pool_length]
  exact PqxdhDeploymentCompileCaps.transported_room bounds budget

end Budget

/-! ### The relation at the cut with owner positions and remaining creations -/

section Indexed
open PqxdhDeploymentIdealParams (Target Params)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- The relation at the cut (`PqxdhDeploymentIdealCut.CutRel`) strengthened by the owner positions and the remaining creations: every owner entry's KEM index is its position, the active KEM key pair of the owner entry at position `j` is pool entry `j` (owner `j` holds pool entry `j`), and at a pending compiled cut the compiled continuation, for every reply of the suspended accept, stays within the budget with only the remaining creations. -/
structure CutRelIndexed {Y : Type} (budget : PqxdhRegistrationJointRevealCosts.SourceKind → ℕ)
    (reached : (CutCE Y × Local) × PqxdhRegistrationJointSchedule.State KemSK) : Prop where
  base : PqxdhDeploymentIdealCut.CutRel setup codec t p created budget reached
  indexed : PqxdhDeploymentIdealCut.PoolIndexed reached.2
  entries : ∀ (j : ℕ) (entry : PqxdhRegistrationJointOwnership.Entry KemSK), reached.2.owners[j]? = some entry →
    ∀ keys, PqxdhRegistrationJointOwnership.activeKey entry.owner = some keys → (p.pool t)[j]? = some keys
  residual : ∀ raw next, PqxdhDeploymentIdealCut.compileCut setup codec route reached.1 = .pending raw next →
    ∀ reply source, (next reply).IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source)
      (Function.update budget (.inl 1) (budget (.inl 1) - reached.2.pool.2.keys.length) source)

/-- Every outcome of the common prefix satisfies the strengthened relation at the cut, under the approved codec contracts, for a Server constructed with the experiment's key ID and no peer whose seed sits at its identity slot of the joint pool, with an empty KEM pool, and for a source budget of the whole compiled program that creates no more KEM keys than the pool holds. -/
theorem cut_relIndexed {Y : Type} (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (sender : created.server.server.metadata.sender = setup.serverKeyId)
    (peers : ∀ kid, created.server.server.peers kid = none) (pool : PqxdhRegistrationJointPreparation.Pool KemSK)
    (empty : pool.2 = PqxdhLiveKemBirth.empty)
    (slot : pool.1.seeds[created.server.server.metadata.identityIndex]? = some created.seed) (work : OracleComp Spec Y)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → ℕ)
    (whole : ∀ source, (PqxdhDeploymentCompile.compile setup codec route work).IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (room : budget (.inl 1) ≤ (p.pool t).length)
    (reached : (CutCE Y × Local) × PqxdhRegistrationJointSchedule.State KemSK)
    (member : reached ∈ support (commonPrefix setup codec route checks t p created pool work)) :
    CutRelIndexed setup codec route t p created budget reached := by
  have certified : ∀ source, (PqxdhRegistrationJointAcceptCut.scan (PqxdhDeploymentCompile.compile setup codec route work)
      t.accept).IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source) :=
    fun source => PqxdhRegistrationJointAcceptCut.scan_bound _ t.accept _ _ (whole source)
  exact ⟨PqxdhDeploymentIdealCut.cut_rel setup codec route checks t p created phase1 phase2 sender peers pool empty slot
      work budget certified room reached member,
    PqxdhDeploymentIdealCut.cut_indexed setup codec route checks t p created pool empty slot work reached member,
    fun j entry found keys active => PqxdhDeploymentIdealCut.cut_entry_key setup codec route checks t p created pool
      empty slot work budget certified room reached member j entry found keys active,
    (PqxdhDeploymentIdealCut.cut_residual setup codec route checks t p created pool empty work budget whole reached
      member).2⟩

end Indexed

/-! ### The reduction of the second compile lemma to the selected-key branch -/

section Reduction
open PqxdhDeploymentBackend (gameWith)
open PqxdhDeploymentIdealSteps (idealReg idealInit idealGame)
open PqxdhDeploymentIdealParams (Target Params drawParams)
open PqxdhDeploymentInterface (Budget FreshBounds Mode ModeSpec asModeO)
open PqxdhDeploymentKemTransfer (Observed happens designated)
open PqxdhDeploymentCompileCaps (transported)
open LazyOracleDiscard (LawEq)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks)

/-- The selected-key branch of the second compile lemma at the challenger's draws `p` (an obligation of unit U6: `PqxdhDeploymentIdealActive.selected_of_active` derives it from the active branch `PqxdhDeploymentIdealActive.ActiveBranch`, which unit U6's post-challenge simulation is to prove): for every constructed Server and every outcome of the common prefix (with the strengthened relation at the cut for the transported budget) whose CE cut is pending at raw bytes that verify to the selected PQ key, item 2's side (`itemRest`) and the CE side (`resumeMarked` with the decision together with the mark) have the same law. -/
def SelectedBranch {A : Type} (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (event : Observed X → Bool)
    (claim : Observed X → Option PqxdhDeploymentInterface.Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) (p : Params KemSK budget.create) : Prop :=
  ∀ (born : Option (PqxdhLiveServerConstruction.Created Unit) × PqxdhRegistrationJointServerPrefix.State KemSK A),
    born ∈ support ((PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId none).run
      ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)) →
    ∀ created, born.1 = some created →
    ∀ reached, reached ∈ support (commonPrefix setup codec route checks (Target.ofCE budget g) p created born.2.1
      (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode adversary))) →
    CutRelIndexed setup codec route (Target.ofCE budget g) p created (transported bounds budget) reached →
    ∀ raw next, reached.1.1 = .pending raw next →
    ∀ value, PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value →
    value.keys.pqKey = p.chosen.1 →
    LawEq (itemRest (Reader := Reader) setup codec route checks (Target.ofCE budget g) p
        (PqxdhDeploymentKemTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (PqxdhRegistrationJointServerBirth.encode created) born.2.2 reached)
      (resumeMarked setup codec route checks (Target.ofCE budget g) p created
        (fun outcome => markedDecision setup codec budget event claim g
          (some (PqxdhRegistrationJointServerBirth.encode created, outcome.1, outcome.2.1, outcome.2.2)))
        reached.1.1 (merge reached.1.2 (PqxdhRegistrationJointSchedule.source reached.2)))

/-- The second compile lemma (design-v2 section 8.1, `ideal_compile`) from its selected-key branch: for a budget-respecting adversary and a CE designation `g`, if the selected-key branch holds at every draw of the challenger, item 2's two-slot ideal world of the compiled program accepts the per-target decision with the probability with which `CE.idealGame g` ends with the event and the claim designating `g`. Everything else is proved here: the draws (`PqxdhDeploymentIdealParams.slotGame_pool`), the prefixes on both sides (`slotGameAt_cut`, `ideal_prefixMarked`), the key match (`game_marked`), a failed construction, a completed cut, and a cut whose raw bytes do not verify to the selected PQ key (`itemRest_dead`, `resumeMarked_dead`), with the transported CE budget (`scan_certified`, `transported_pool`, `PqxdhDeploymentCompileCaps.compile_full_certified`). Premises: the approved codec contracts `Phase1ReadBack` and `Phase2ReadBack` and the budget. -/
theorem ideal_compile_of_selected {A : Type} (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (event : Observed X → Bool)
    (claim : Observed X → Option PqxdhDeploymentInterface.Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A)
    (selected : ∀ p ∈ support (drawParams setup budget.create),
      SelectedBranch (Reader := Reader) setup codec route checks ensureInit bounds mode adversary budget event claim g
        runtime p) :
    𝒟[PqxdhRegistrationJointKemSecondEntry.slotGame setup codec checks ensureInit none
        (PqxdhDeploymentKemTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary) runtime budget.create
        (PqxdhDeploymentKemTransfer.selectedKem budget g) g.1.val 2] {true} =
      𝒟[(fun outcome => decide (happens event (classicalOf outcome) = true ∧
          designated setup.source.crypto codec setup.serverKeyId budget claim (classicalOf outcome) = some g)) <$>
        (idealGame setup codec route checks budget g ensureInit bounds mode adversary).run runtime] {true} := by
  set work := PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode adversary)
    with workEq
  have perDraw : ∀ p ∈ support (drawParams setup budget.create),
      LawEq (PqxdhDeploymentIdealParams.slotGameAt (Reader := Reader) setup codec checks ensureInit none
          (PqxdhDeploymentKemTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
          (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary) runtime budget.create
          (PqxdhDeploymentKemTransfer.selectedKem budget g) g.1.val 2 p)
        (ceDecide setup codec budget event claim g <$>
          (gameWith setup codec route idealInit (idealReg setup codec route checks (Target.ofCE budget g) p) ensureInit 0
            bounds mode adversary).run runtime) := by
    intro p drawn
    rw [show PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary =
        PqxdhDeploymentCompile.compile setup codec route work from rfl,
      show PqxdhDeploymentKemTransfer.selectedKem budget g = (Target.ofCE budget g).kem from rfl,
      show g.1.val = (Target.ofCE budget g).accept from rfl,
      slotGameAt_cut setup codec route checks (Target.ofCE budget g) p _ ensureInit work runtime
        (transported bounds budget) (scan_certified setup codec route bounds mode adversary budget respects _)
        (transported_unread bounds budget).1 (transported_unread bounds budget).2
        (transported_pool bounds budget (Target.ofCE budget g) p),
      game_marked setup codec route checks phase1 budget event claim g p ensureInit bounds mode adversary runtime,
      ideal_prefixMarked setup codec route checks (Target.ofCE budget g) p phase1 phase2 ensureInit bounds mode adversary
        runtime]
    refine PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun born bornMember => ?_
    rcases born with ⟨_ | created, after⟩
    · exact LawEq.of_eq (by rw [itemPost_failed]; rfl)
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
          (cut_relIndexed setup codec route checks (Target.ofCE budget g) p created phase1 phase2 sender peers after.1
            empty slot work (transported bounds budget)
            (PqxdhDeploymentCompileCaps.compile_full_certified setup codec route bounds mode adversary budget respects)
            (transported_pool bounds budget (Target.ofCE budget g) p) reached reachedMember)
          raw next pending value verified matched
      · have dead : ∀ raw next, reached.1.1 = .pending raw next → ∀ value,
            PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value →
              value.keys.pqKey ≠ p.chosen.1 :=
          fun raw next pending value verified matched => active ⟨raw, next, value, pending, verified, matched⟩
        exact (itemRest_dead setup codec route checks (Target.ofCE budget g) p
          (PqxdhDeploymentKemTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
          (PqxdhRegistrationJointServerBirth.encode created) after.2 reached dead).trans
          (resumeMarked_dead setup codec route checks (Target.ofCE budget g) p created
            (fun outcome : (X × PqxdhDeploymentSecrecy.Ledger) × PqxdhDeploymentNative.State KemSK =>
              decide (event (outcome.1.1, outcome.1.2, outcome.2.produced) = true ∧
              PqxdhDeploymentKemTransfer.target setup.source.crypto codec setup.serverKeyId budget claim
                (outcome.1.1, outcome.1.2, outcome.2.produced) = some g))
            reached.1.1 (merge reached.1.2 (PqxdhRegistrationJointSchedule.source reached.2)) dead).symm
  have total := (PqxdhDeploymentSeedSplit.LawEq.bind_support (drawParams setup budget.create) perDraw).evalDist_eq
  rw [PqxdhDeploymentIdealParams.slotGame_pool, total]
  congr 2
  simp only [idealGame, StateT.run, map_bind]
  rfl

end Reduction

end BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.ideal_cutMarked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.ideal_cutMarked

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.ideal_prefixMarked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.ideal_prefixMarked

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.game_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.game_marked

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.slotGameAt_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.slotGameAt_cut

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.itemPost_failed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.itemPost_failed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.itemPost_dead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.itemPost_dead

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.optionRun_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.optionRun_support

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.rejectRun_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.rejectRun_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.opaqueRest_dead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.opaqueRest_dead

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.itemRest_dead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.itemRest_dead

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.map_const_lawEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.map_const_lawEq

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.resumeMarked_dead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.resumeMarked_dead

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.scan_certified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.scan_certified

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.transported_unread' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.transported_unread

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.transported_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.transported_pool

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.cut_relIndexed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.cut_relIndexed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.ideal_compile_of_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch.ideal_compile_of_selected

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItemRun

/-!
# The active branch from the CE side of the middle invariant (CE-11b, unit U6, fourth part)

The active branch of the second compile lemma (`PqxdhDeploymentIdealActive.ActiveBranch`) compares item 2's post-challenge phase on an active cut with the CE side from the selected accept's steps after encapsulation (`activeCE`). `PqxdhDeploymentIdealPostItemRun.itemPost_middle` writes item 2's side as the middle run. This module writes the CE side as the merge image of the same middle run and compares the decisions, so the active branch, and with it the second compile lemma, follows from the CE side of the invariant of the middle execution alone.

- `copiesAfter` (the local copies after the selected accept), `cutMid` (the middle state at the cut), `decision_reset` (a decision on the result and the deployment state does not see the LQ-F ghosts of the starting state) and `activeCE_middle`: the CE side is the ideal registration's steps after encapsulation on the native state of the annotated source state at the cut through the allocator, then the compiled continuation under the middle source handler from the middle state after the selected accept, with the copies merged into the final state (through `PqxdhDeploymentIdealPostMark.activeCE_reply`, `PqxdhDeploymentIdealPostSource.selectedStep_merge` with `acceptAfter_comm`, and `compile_simulationMid`), for an invariant of the middle execution with the premises of `compile_simulationMid`.
- `decision_merge`: item 2's tagged decision and the CE decision together with the mark agree on the merge image (the produced frames of the merge are those of the local copies).
- `MiddleInv` and `MiddleStart`: the CE side of the middle invariant, one per constructed Server: it implies CE-3's merge invariant, every compiled step keeps it, and it holds after the selected accept on every outcome of every active cut.
- `activeBranch_of_middle`: `ActiveBranch` from `MiddleInv` and `MiddleStart`, with item 2's premises from the Server's construction and the strengthened relation at the cut (`PqxdhDeploymentIdealBranch.CutRelIndexed`); `ideal_compile_of_middle`: the second compile lemma from them at every draw of the challenger, through `PqxdhDeploymentIdealActive.ideal_compile_of_active`.

These are program equalities and reductions. They charge nothing and make no security claim; `MiddleInv` and `MiddleStart` are obligations of the unit, not assumptions of a published claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealPostReduce
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealPostSource (Mid sourceMid mergeX)
open PqxdhDeploymentIdealPostItemRun (AcceptRun afterSelected)
open PqxdhDeploymentCompile (Local merge compileImpl)

/-! ### The CE side of the active branch as the merge image of the middle run -/

section CE
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- The local copies after the selected accept: the accept's reply logged. -/
def copiesAfter (copies : Local) (raw : Pqxdh.Bytes) (answer : Option ℕ) : Local :=
  { copies with log := PqxdhDeploymentCompile.logReply copies.log (.accept raw) answer }

/-- The middle state at the cut: the annotated source state, the ideal backend right before the selected accept and no seed. -/
def cutMid (joint : PqxdhRegistrationJointSchedule.State KemSK) : Mid KemSK :=
  ⟨joint, PqxdhDeploymentIdealCut.withAccepts (PqxdhDeploymentIdealSteps.idealInit created) t.accept, ∅⟩

/-- A decision that reads the result and the deployment state does not see the LQ-F ghosts of the starting state of a run of the handler with the ideal registration. -/
theorem decision_reset {Y : Type} (decision : Y × PqxdhDeploymentNative.State KemSK × Bool → Bool) (marked : Bool)
    (work : OracleComp PqxdhDeploymentInterface.Spec Y)
    (start : PqxdhDeploymentBackend.XState KemSK (PqxdhDeploymentIdealSteps.IdealBk PqxdhDeploymentIdealSteps.TableState) 2)
    (target : PqxdhDeploymentBackend.XState KemSK (PqxdhDeploymentIdealSteps.IdealBk PqxdhDeploymentIdealSteps.TableState) 2)
    (same : PqxdhDeploymentIdealCut.unghost start = target) :
    (fun outcome => decision (outcome.1, outcome.2.base, marked)) <$>
        (simulateQ (PqxdhDeploymentBackend.handlerWith setup codec route
          (PqxdhDeploymentIdealSteps.idealReg setup codec route checks t p created)) work).run start =
      (fun outcome => decision (outcome.1, outcome.2.base, marked)) <$>
        (Prod.map id PqxdhDeploymentIdealCut.unghost <$> (simulateQ (PqxdhDeploymentBackend.handlerWith setup codec route
          (PqxdhDeploymentIdealSteps.idealReg setup codec route checks t p created)) work).run target) := by
  have reset := PqxdhDeploymentIdealCut.run_reset (PqxdhDeploymentBackend.handlerWith setup codec route
    (PqxdhDeploymentIdealSteps.idealReg setup codec route checks t p created)) PqxdhDeploymentIdealCut.unghost
    (fun _ => rfl) (fun query state => PqxdhDeploymentIdealCut.idealStep_unghost setup codec route checks t p created
      query state) work start
  rw [same] at reset
  rw [← reset, Functor.map_map]
  rfl

/-- The CE side of the active branch is the merge image of the middle run: the ideal registration's steps after encapsulation through the allocator on the native state of the annotated source state at the cut, then the compiled continuation under the middle source handler from the middle state after the selected accept, with the local copies after the accept merged into its final state. It needs an invariant of the middle execution that implies CE-3's merge invariant, is kept by every compiled step and holds after the selected accept (the premises of `PqxdhDeploymentIdealPostSource.compile_simulationMid`). -/
theorem activeCE_middle {Y : Type} (decision : Y × PqxdhDeploymentNative.State KemSK × Bool → Bool) (copies : Local)
    (joint : PqxdhRegistrationJointSchedule.State KemSK) (raw : Pqxdh.Bytes)
    (next : Option ℕ → OracleComp PqxdhDeploymentInterface.Spec Y) (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes) (consumed : List Pqxdh.Bytes)
    (logged : Option PqxdhJointGapDh.ScalarBytes) (good : Local → Mid KemSK → Prop)
    (sound : ∀ copies m, good copies m →
      PqxdhDeploymentCompileStep.Inv setup codec copies (PqxdhRegistrationJointSchedule.source m.joint))
    (preserved : ∀ query copies m, good copies m →
      ∀ result ∈ support ((PqxdhDeploymentIdealPostSource.compiledMid setup codec route checks t p created query).run
        (copies, m)), good result.2.1 result.2.2)
    (start : ∀ w ∈ support ((simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
        ((PqxdhDeploymentIdealActive.acceptAfter setup codec checks created.seed p.challenge value ephemeral consumed
          logged).run joint.shared)).run (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial)),
      good (copiesAfter copies raw w.1.1.1.1) (afterSelected t joint w)) :
    PqxdhDeploymentIdealActive.activeCE setup codec route checks t p created decision
        (merge copies (PqxdhRegistrationJointSchedule.source joint)) next value ephemeral consumed logged =
      (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
          ((PqxdhDeploymentIdealActive.acceptAfter setup codec checks created.seed p.challenge value ephemeral consumed
            logged).run joint.shared)).run
          (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial) >>= fun w =>
        (fun result => decision (result.1.1, (mergeX result.1.2 result.2).base, w.1.1.1.1.isSome)) <$>
          (simulateQ (sourceMid setup codec route checks t p created)
            ((simulateQ (compileImpl setup codec route) (next w.1.1.1.1)).run (copiesAfter copies raw w.1.1.1.1))).run
            (afterSelected t joint w) := by
  rw [PqxdhDeploymentIdealPostMark.activeCE_reply]
  unfold PqxdhDeploymentIdealPostMark.activeReply
  have mergedStart : PqxdhDeploymentIdealSlots.detach (PqxdhDeploymentIdealCut.cutState t created
      (merge copies (PqxdhRegistrationJointSchedule.source joint))) =
      PqxdhDeploymentIdealPostSource.mergeY copies (PqxdhDeploymentIdealSlots.detach
        (PqxdhDeploymentIdealPostSource.toX (cutMid t created joint))) := rfl
  rw [mergedStart, PqxdhDeploymentIdealPostSource.selectedStep_merge copies _
    (PqxdhDeploymentIdealPostSource.acceptAfter_comm copies setup codec checks created.seed p.challenge value ephemeral
      consumed logged)]
  rw [simulateQ_map, StateT.run_map, bind_map_left,
    show (PqxdhDeploymentIdealActive.selectedStep (PqxdhDeploymentIdealActive.acceptAfter setup codec checks created.seed
      p.challenge value ephemeral consumed logged)).run (PqxdhDeploymentIdealSlots.detach
        (PqxdhDeploymentIdealPostSource.toX (cutMid t created joint))) = _ <$>
      (PqxdhDeploymentIdealActive.acceptAfter setup codec checks created.seed p.challenge value ephemeral consumed
        logged).run joint.shared from rfl,
    simulateQ_map, StateT.run_map, bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun w member => ?_
  have sim := PqxdhDeploymentIdealPostSource.compile_simulationMid setup codec route checks t p created good sound preserved
    (next w.1.1.1.1) (copiesAfter copies raw w.1.1.1.1) (afterSelected t joint w) (start w member)
  refine (decision_reset setup codec route checks t p created decision _ (next w.1.1.1.1) _
    (mergeX (copiesAfter copies raw w.1.1.1.1) (afterSelected t joint w)) ?_).trans ?_
  · rfl
  · rw [← sim, Functor.map_map]
    rfl

end CE

/-! ### The active branch from the CE side of the middle invariant -/

section Reduction
open PqxdhDeploymentInterface (Budget FreshBounds Mode ModeSpec asModeO)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentCompileCaps (transported)
open LazyOracleDiscard (LawEq)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks)

/-- The decision of item 2's tagged continuation and the CE decision together with the mark agree on the merge image: both read the event and the designation on the result with the produced frames of the local copies, and whether the selected accept returned a session. -/
theorem decision_merge (budget : Budget) (event : Observed X → Bool)
    (claim : Observed X → Option PqxdhDeploymentInterface.Handle) (g : Fin budget.accept × Fin budget.capacity)
    (created : PqxdhLiveServerConstruction.Created Unit) (raw : Pqxdh.Bytes) (answer : Option ℕ)
    (result : ((X × PqxdhDeploymentSecrecy.Ledger) × Local) × Mid KemSK) :
    PqxdhRegistrationJointAcceptCutTag.decideTag
        (PqxdhDeploymentKemTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (result.1, some (raw, answer)) =
      PqxdhDeploymentIdealBranch.markedDecision setup codec budget event claim g
        (some (PqxdhRegistrationJointServerBirth.encode created, result.1.1, (mergeX result.1.2 result.2).base,
          answer.isSome)) := by
  rcases answer with _ | session
  · simp [PqxdhRegistrationJointAcceptCutTag.decideTag, PqxdhRegistrationJointAcceptCutTag.accepted,
      PqxdhDeploymentIdealBranch.markedDecision]
  · have produced : (mergeX result.1.2 result.2).base.produced = result.1.2.produced := rfl
    simp only [PqxdhRegistrationJointAcceptCutTag.decideTag, PqxdhRegistrationJointAcceptCutTag.accepted,
      PqxdhDeploymentIdealBranch.markedDecision, PqxdhDeploymentKemTransfer.decision,
      PqxdhDeploymentKemTransfer.observeCompiled, Option.isSome_some, Bool.and_true, produced]
    cases event (result.1.1.1, result.1.1.2, result.1.2.produced) <;> simp
    exact decide_eq_decide.mpr Iff.rfl

/-- The CE side of the invariant of the middle execution, for one constructed Server: it implies CE-3's merge invariant on the local copies and the annotated source state, and every compiled step under the middle source handler keeps it (the premises `sound` and `preserved` of `PqxdhDeploymentIdealPostSource.compile_simulationMid`). -/
structure MiddleInv {count : ℕ} (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (inv : Local → Mid KemSK → Prop) : Prop where
  sound : ∀ copies m, inv copies m →
    PqxdhDeploymentCompileStep.Inv setup codec copies (PqxdhRegistrationJointSchedule.source m.joint)
  preserved : ∀ query copies m, inv copies m →
    ∀ result ∈ support ((PqxdhDeploymentIdealPostSource.compiledMid setup codec route checks t p created query).run
      (copies, m)), inv result.2.1 result.2.2

/-- The start of the CE side of the middle invariant: on every active cut of the experiment (the binders of `PqxdhDeploymentIdealActive.ActiveBranch`), the invariant of the constructed Server holds after the selected accept, with the local copies after the accept, on every outcome of the steps after encapsulation. -/
def MiddleStart {A : Type} (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) (p : Params KemSK budget.create)
    (inv : PqxdhLiveServerConstruction.Created Unit → Local → Mid KemSK → Prop) : Prop :=
  ∀ (born : Option (PqxdhLiveServerConstruction.Created Unit) × PqxdhRegistrationJointServerPrefix.State KemSK A),
    born ∈ support ((PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId none).run
      ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)) →
    ∀ created, born.1 = some created →
    ∀ reached, reached ∈ support (PqxdhDeploymentIdealCut.commonPrefix setup codec route checks (Target.ofCE budget g) p
      created born.2.1 (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds
        (asModeO mode adversary))) →
    PqxdhDeploymentIdealBranch.CutRelIndexed setup codec route (Target.ofCE budget g) p created
      (transported bounds budget) reached →
    ∀ raw next, reached.1.1 = .pending raw next →
    ∀ value, PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value →
    value.keys.pqKey = p.chosen.1 →
    ∀ pre, pre ∈ support ((simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup codec checks created.seed)
      (PqxdhDeploymentLaterServerSource.beforeLogged (Shared := PqxdhBeaconPhase2Preparation.Word32) value)).run
        reached.2.shared.2.server.consumed) →
    ∀ ephemeral, pre.1.1 = some ephemeral →
    ∀ w ∈ support ((simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
      ((PqxdhDeploymentIdealActive.acceptAfter setup codec checks created.seed p.challenge value ephemeral pre.2
        pre.1.2).run reached.2.shared)).run
          (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial)),
    inv created (copiesAfter reached.1.2 raw w.1.1.1.1) (afterSelected (Target.ofCE budget g) reached.2 w)

/-- The active branch (`PqxdhDeploymentIdealActive.ActiveBranch`) from the CE side of the invariant of the middle execution: a family of invariants, one per constructed Server, that implies CE-3's merge invariant and is kept by every compiled step under the middle source handler (`MiddleInv`), and holds after the selected accept on every outcome of the steps after encapsulation of every active cut (`MiddleStart`). Item 2's side is `PqxdhDeploymentIdealPostItemRun.itemPost_middle`, with item 2's facts at the pool and the continuation's bounds from the strengthened relation at the cut; the CE side is `activeCE_middle`; the two decisions agree on the merge image (`decision_merge`). -/
theorem activeBranch_of_middle {A : Type} (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (event : Observed X → Bool)
    (claim : Observed X → Option PqxdhDeploymentInterface.Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) (p : Params KemSK budget.create)
    (inv : PqxdhLiveServerConstruction.Created Unit → Local → Mid KemSK → Prop)
    (kept : ∀ created, MiddleInv setup codec route checks (Target.ofCE budget g) p created (inv created))
    (start : MiddleStart (Reader := Reader) setup codec route checks ensureInit bounds mode adversary budget g runtime p
      inv) :
    PqxdhDeploymentIdealActive.ActiveBranch (Reader := Reader) setup codec route checks ensureInit bounds mode adversary
      budget event claim g runtime p := by
  intro born bornMember created constructed reached reachedMember related raw next pending value verified matched pre
    preMember ephemeral found
  apply LawEq.of_eq
  have identity : created.publicIdentity = setup.joint.publicKeys created.seed := by
    have bornCreated : (some created, born.2) ∈ support ((PqxdhRegistrationJointServerBirth.source setup.joint ensureInit
        setup.serverKeyId none).run ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)) := by
      rw [← constructed]
      exact bornMember
    exact PqxdhRegistrationJointInitializedAccept.source_public setup.joint ensureInit setup.serverKeyId none _ born.2
      created bornCreated
  have cutEq : PqxdhDeploymentIdealCut.compileCut setup codec route reached.1 =
      .pending raw (PqxdhDeploymentIdealActive.compiledNext setup codec route raw next reached.1.2) := by
    rcases reached with ⟨⟨cut, copies⟩, state⟩
    simp only at pending
    subst pending
    rfl
  have residual := related.residual raw _ cutEq
  have kindBound : ∀ answer (source : PqxdhRegistrationJointRevealCosts.SourceKind),
      (PqxdhDeploymentIdealActive.compiledNext setup codec route raw next reached.1.2 answer).IsQueryBoundP
        (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source)
        (Function.update (transported bounds budget) (.inl 1)
          (transported bounds budget (.inl 1) - reached.2.pool.2.keys.length) source) := residual
  have onlyAllowed : ∀ answer, (PqxdhDeploymentIdealActive.compiledNext setup codec route raw next reached.1.2
      answer).IsQueryBoundP (fun query => ¬ PqxdhDeploymentIdealPostInvariant.Allowed (KemSK := KemSK) query) 0 := by
    intro answer
    have first := kindBound answer (.inr 0)
    have second := kindBound answer (.inr 1)
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, Function.update_of_ne] at first second
    have zero : ∀ field, field = (0 : Fin 5) ∨ field = 1 → transported bounds budget (.inr field) = 0 := by
      rintro field (rfl | rfl) <;> rfl
    rw [zero 0 (Or.inl rfl)] at first
    rw [zero 1 (Or.inr rfl)] at second
    refine (isQueryBoundP_congr_pred (fun query => ?_)).mpr
      (PqxdhDeploymentIdealPostSource.bound_or_zero _ _ _ first second)
    simp only [PqxdhDeploymentIdealPostInvariant.Allowed, not_and_or, not_not]
  have bounded : ∀ answer, (PqxdhDeploymentIdealActive.compiledNext setup codec route raw next reached.1.2
      answer).IsQueryBoundP (PqxdhDeploymentIdealPostInvariant.Costly (KemSK := KemSK))
        (budget.create - reached.2.pool.2.keys.length) := by
    intro answer
    have created := kindBound answer (.inl 1)
    simp only [Function.update_self] at created
    exact created
  have fits : budget.create - reached.2.pool.2.keys.length ≤
      (p.pool (Target.ofCE budget g)).length - reached.2.pool.2.keys.length := by
    have length : (p.pool (Target.ofCE budget g)).length = budget.create + 1 := by
      simp [PqxdhDeploymentIdealParams.pool_eq]
    omega
  rw [PqxdhDeploymentIdealPostItemRun.itemPost_middle setup codec route checks (Target.ofCE budget g) p
      (PqxdhDeploymentKemTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g) created
      identity raw value matched ephemeral pre.2 pre.1.2 reached.2 related.base.owned related.base.prefixed related.indexed
      _ onlyAllowed _ bounded fits born.2.2,
    activeCE_middle setup codec route checks (Target.ofCE budget g) p created _ reached.1.2 reached.2 raw next value
      ephemeral pre.2 pre.1.2 (inv created) (kept created).sound (kept created).preserved
      (start born bornMember created constructed reached reachedMember related raw next pending value verified matched pre
        preMember ephemeral found)]
  refine bind_congr fun w => ?_
  unfold PqxdhRegistrationJointAcceptKemCut.tagged
  rw [simulateQ_map, StateT.run_map, Functor.map_map]
  refine congrArg (fun f => f <$> _) (funext fun result => ?_)
  exact decision_merge setup codec budget event claim g created raw w.1.1.1.1 result

/-- The second compile lemma (design-v2 section 8.1) from the CE side of the middle invariant at every draw of the challenger: `PqxdhDeploymentIdealActive.ideal_compile_of_active` with `activeBranch_of_middle`. Premises: the approved codec contracts, the budget, and at every draw an invariant family that is kept (`MiddleInv`) and holds after the selected accept (`MiddleStart`). -/
theorem ideal_compile_of_middle {A : Type} (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (event : Observed X → Bool)
    (claim : Observed X → Option PqxdhDeploymentInterface.Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) (inv : Params KemSK budget.create → PqxdhLiveServerConstruction.Created Unit → Local → Mid KemSK → Prop)
    (kept : ∀ p ∈ support (PqxdhDeploymentIdealParams.drawParams setup budget.create), ∀ created,
      MiddleInv setup codec route checks (Target.ofCE budget g) p created (inv p created))
    (start : ∀ p ∈ support (PqxdhDeploymentIdealParams.drawParams setup budget.create),
      MiddleStart (Reader := Reader) setup codec route checks ensureInit bounds mode adversary budget g runtime p (inv p)) :
    𝒟[PqxdhRegistrationJointKemSecondEntry.slotGame setup codec checks ensureInit none
        (PqxdhDeploymentKemTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary) runtime budget.create
        (PqxdhDeploymentKemTransfer.selectedKem budget g) g.1.val 2] {true} =
      𝒟[(fun outcome => decide (PqxdhDeploymentKemTransfer.happens event
          (PqxdhDeploymentIdealBranch.classicalOf outcome) = true ∧
          PqxdhDeploymentKemTransfer.designated setup.source.crypto codec setup.serverKeyId budget claim
            (PqxdhDeploymentIdealBranch.classicalOf outcome) = some g)) <$>
        (PqxdhDeploymentIdealSteps.idealGame setup codec route checks budget g ensureInit bounds mode adversary).run
          runtime] {true} :=
  PqxdhDeploymentIdealActive.ideal_compile_of_active setup codec route checks phase1 phase2 ensureInit bounds mode
    adversary budget respects event claim g runtime fun p drawn =>
      activeBranch_of_middle setup codec route checks ensureInit bounds mode adversary budget event claim g runtime p
        (inv p) (kept p drawn) (start p drawn)

end Reduction

end BeaconcryptCore.Computational.PqxdhDeploymentIdealPostReduce

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostReduce.decision_reset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostReduce.decision_reset

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostReduce.activeCE_middle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostReduce.activeCE_middle

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostReduce.decision_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostReduce.decision_merge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostReduce.activeBranch_of_middle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostReduce.activeBranch_of_middle

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostReduce.ideal_compile_of_middle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostReduce.ideal_compile_of_middle

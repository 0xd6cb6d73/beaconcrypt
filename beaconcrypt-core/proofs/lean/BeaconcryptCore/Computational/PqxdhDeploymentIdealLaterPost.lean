-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps

/-! LQ-F upstream, unit B2: the active branch of the later second compile lemma (the logged counterpart of CE-11b unit U6's `PqxdhDeploymentIdealPostReduce`, the start of `PqxdhDeploymentIdealPostGood` and `PqxdhDeploymentIdealPost`). `PqxdhDeploymentIdealLaterBranch` reduced the frozen target `PqxdhDeploymentIdealLaterGame.IdealCompileServerTarget` to the active branch `ActiveBranchL` at every draw of the challenger; `active_branchL` proves it.

- The CE side: `startL` (the logged middle state after the selected accept, with the compiled program's snapshot and local copies) and `activeCE_middleL`: the CE side of the active branch (`PqxdhDeploymentIdealLaterBranch.activeCEL`) is the ideal registration's steps after encapsulation through the allocator, then the logged continuation `compiledNextL` under the logged middle source handler, read off through the merge image, with the mark replaced by whether the selected accept returned a session (CE-11b's `selectedStep_merge` and `acceptAfter_comm` for the selected step, `acceptAfter_mark`, `run_settled` and `PqxdhDeploymentIdealLaterBranch.laterTail_marks` for the mark, `PqxdhDeploymentIdealLaterMid.compile_simulationMidL` for the run part and `PqxdhDeploymentIdealLaterMid.laterTail_middle` for the rest).
- `decision_mergeL`: item 2's tagged decision of the compiled LQ-F program and the later decision together with the mark agree on the merge image.
- The bounds of the logged continuation: `embed_bound`, `post_zeroK`, `restOf_bound`, `restOf_allowed` (the terminal reads, the Server read and the post part read no KEM field) and `restOf_costly` (and create nothing); the run part's bounds come from the relation at the cut (`PqxdhDeploymentIdealLaterCut.CutRelL.residual` with `PqxdhDeploymentIdealLaterBranch.runBudget_caps`).
- The start after the selected accept: `acceptAfter_logged` (the accept's logged entry is the given scalar, which `PqxdhDeploymentLaterServerSource.beforeLogged_some` identifies with the ephemeral's secret, the entry item 2's resumption appends), `start_goodL` (`GoodMidL`, CE-11b's `middleStart`), `start_itemL` (item 2's invariant) and `run_slotL` (the Server's identity slot holds its seed on every state reached by the run part, by item 2's invariant through `PqxdhDeploymentIdealLaterSteps.simulate_keeps`).
- `active_branchL`: item 2's side by `PqxdhDeploymentIdealLaterSteps.itemPost_middleL`, the CE side by `activeCE_middleL`, the logged entries agree, and the decisions agree on the merge image.

Premises: the approved codec contracts `Phase1ReadBack` and `Phase2ReadBack`. These are program equalities, support facts and query bounds. They charge nothing and make no security claim. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPost
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentCompile (Local merge compileImpl)
open PqxdhDeploymentCompileInvariant (Good)
open PqxdhDeploymentLater (Snap PostSpec)
open PqxdhDeploymentLaterCompile (compileSnapImpl)
open PqxdhDeploymentLaterServerSource (Log embed)
open PqxdhDeploymentBackend (XState handlerWith)
open PqxdhDeploymentIdealSteps (IdealBk TableState idealReg)
open PqxdhDeploymentIdealSlots (detach)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealPostSource (mergeY)
open PqxdhDeploymentIdealPostReduce (copiesAfter)
open PqxdhDeploymentIdealPostItemRun (AcceptRun afterSelected)
open PqxdhDeploymentIdealLaterMid (MidL sourceMidL compiledMidL mergeXL GoodMidL)
open PqxdhRegistrationJointRevealCosts (sourceKind)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-! ### The CE side of the active branch as a function of the logged middle run -/

section CE
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- The logged middle state after the selected accept, with the compiled program's snapshot and local copies: the snapshot at the cut, the local copies after the accept (its reply logged), CE-11b's middle state after the selected accept (`PqxdhDeploymentIdealPostItemRun.afterSelected`) and the log at the cut with the accept's logged entry. -/
def startL (snap : Snap) (copies : Local) (joint : PqxdhRegistrationJointSchedule.State KemSK) (log : Log)
    (raw : Pqxdh.Bytes) (w : AcceptRun KemSK) : (Snap × Local) × MidL KemSK :=
  ((snap, copiesAfter copies raw w.1.1.1.1), (afterSelected t joint w, log ++ [w.1.1.1.2]))

/-- The CE side of the active branch is a function of the logged middle run: the ideal registration's steps after encapsulation through the allocator on the shared state at the cut, then the logged continuation `PqxdhDeploymentIdealLaterBranch.compiledNextL` under the logged middle source handler from the logged middle state after the selected accept, read off through the merge image, with the mark replaced by whether the selected accept returned a session (`PqxdhDeploymentIdealPostMark.acceptAfter_mark`, `PqxdhDeploymentIdealKeymatch.run_settled`, `PqxdhDeploymentIdealLaterBranch.laterTail_marks`). The run part is `PqxdhDeploymentIdealLaterMid.compile_simulationMidL` and the rest `PqxdhDeploymentIdealLaterMid.laterTail_middle`. Premises: `GoodMidL` after the selected accept, and the Server's identity slot holding its seed on every state reached by the compiled run part. -/
theorem activeCE_middleL {A X Out : Type} (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (decision : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out ×
      PqxdhDeploymentLaterServerGame.LaterState KemSK) × A → Bool → Bool)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (after : A) (snap : Snap)
    (copies : Local) (joint : PqxdhRegistrationJointSchedule.State KemSK) (log : Log) (raw : Pqxdh.Bytes)
    (next : Option ℕ → OracleComp Spec (X × PqxdhDeploymentSecrecy.Ledger))
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes) (consumed : List Pqxdh.Bytes)
    (logged : Option PqxdhJointGapDh.ScalarBytes)
    (good : ∀ w ∈ support ((simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
        ((PqxdhDeploymentIdealActive.acceptAfter setup codec checks created.seed p.challenge value ephemeral consumed
          logged).run joint.shared)).run (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial)),
      GoodMidL setup codec t (startL t snap copies joint log raw w))
    (slot : ∀ w ∈ support ((simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
        ((PqxdhDeploymentIdealActive.acceptAfter setup codec checks created.seed p.challenge value ephemeral consumed
          logged).run joint.shared)).run (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial)),
      ∀ r ∈ support ((simulateQ (compiledMidL setup codec route checks t p created) (next w.1.1.1.1)).run
        (startL t snap copies joint log raw w)),
      r.2.2.1.joint.pool.1.seeds[created.server.server.metadata.identityIndex]? = some created.seed) :
    PqxdhDeploymentIdealLaterBranch.activeCEL setup codec route checks t p created decision second after
        (snap, (merge copies (PqxdhRegistrationJointSchedule.source joint), log)) next value ephemeral consumed logged =
      (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
          ((PqxdhDeploymentIdealActive.acceptAfter setup codec checks created.seed p.challenge value ephemeral consumed
            logged).run joint.shared)).run
          (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial) >>= fun w =>
        (fun result => decision (some (PqxdhRegistrationJointServerBirth.encode created, result.1.1,
            (result.1.2.1, (result.1.2.2.1, (merge result.1.2.2.2 (PqxdhRegistrationJointSchedule.source result.2.1.joint),
              result.2.2)))), after) w.1.1.1.1.isSome) <$>
          (simulateQ (sourceMidL setup codec route checks t p created)
            (PqxdhDeploymentIdealLaterBranch.compiledNextL setup codec route second raw next (snap, copies)
              w.1.1.1.1)).run (startL t snap copies joint log raw w).2 := by
  unfold PqxdhDeploymentIdealLaterBranch.activeCEL
  have mergedStart : detach (PqxdhDeploymentIdealLaterCut.cutStateL t created
      (snap, (merge copies (PqxdhRegistrationJointSchedule.source joint), log))) =
      mergeY copies (detach (⟨⟨PqxdhRegistrationJointSchedule.source joint, 0, fun _ => 0, []⟩,
        PqxdhDeploymentIdealCut.withAccepts (PqxdhDeploymentIdealSteps.idealInit created) t.accept, ∅, snap, log⟩ :
          XState KemSK (IdealBk TableState) 2)) := rfl
  rw [map_bind, bind_assoc, mergedStart, PqxdhDeploymentIdealPostSource.selectedStep_merge copies _
    (PqxdhDeploymentIdealPostSource.acceptAfter_comm copies setup codec checks created.seed p.challenge value ephemeral
      consumed logged)]
  rw [bind_map_left, show (PqxdhDeploymentIdealActive.selectedStep (PqxdhDeploymentIdealActive.acceptAfter setup codec
      checks created.seed p.challenge value ephemeral consumed logged)).run (detach (⟨⟨PqxdhRegistrationJointSchedule.source
        joint, 0, fun _ => 0, []⟩, PqxdhDeploymentIdealCut.withAccepts (PqxdhDeploymentIdealSteps.idealInit created)
          t.accept, ∅, snap, log⟩ : XState KemSK (IdealBk TableState) 2)) =
      _ <$> (PqxdhDeploymentIdealActive.acceptAfter setup codec checks created.seed p.challenge value ephemeral consumed
        logged).run joint.shared from rfl]
  simp only [simulateQ_map, StateT.run_map, bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun w member => ?_
  show (simulateQ (handlerWith setup codec route (idealReg setup codec route checks t p created)) (next w.1.1.1.1)).run
      (mergeXL (startL t snap copies joint log raw w)) >>= (fun z => (fun outcome =>
        decision (PqxdhDeploymentIdealLaterGame.laterOf outcome) (PqxdhDeploymentIdealLaterCut.markedL outcome)) <$>
          PqxdhDeploymentFinishErasure.laterTail (PqxdhDeploymentFinishErasure.realPost setup codec checks) created second
            id after z) = _
  have produced : w.1 ∈ support ((PqxdhDeploymentIdealActive.acceptAfter setup codec checks created.seed p.challenge value
      ephemeral consumed logged).run joint.shared) := by
    apply OracleComp.support_simulateQ_run'_subset
      (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService) _
      (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial)
    rw [StateT.run'_eq, support_map]
    exact ⟨w, member, rfl⟩
  have mark := (PqxdhDeploymentIdealPostMark.acceptAfter_mark setup codec checks created.seed p.challenge value ephemeral
    consumed logged joint.shared w.1 produced).2
  have marked : ((simulateQ (handlerWith setup codec route (idealReg setup codec route checks t p created))
      (next w.1.1.1.1)).run (mergeXL (startL t snap copies joint log raw w)) >>= fun z => (fun outcome =>
        decision (PqxdhDeploymentIdealLaterGame.laterOf outcome) (PqxdhDeploymentIdealLaterCut.markedL outcome)) <$>
          PqxdhDeploymentFinishErasure.laterTail (PqxdhDeploymentFinishErasure.realPost setup codec checks) created second
            id after z) =
      ((simulateQ (handlerWith setup codec route (idealReg setup codec route checks t p created))
        (next w.1.1.1.1)).run (mergeXL (startL t snap copies joint log raw w)) >>= fun z => (fun outcome =>
          decision (PqxdhDeploymentIdealLaterGame.laterOf outcome) w.1.1.1.1.isSome) <$>
            PqxdhDeploymentFinishErasure.laterTail (PqxdhDeploymentFinishErasure.realPost setup codec checks) created
              second id after z) := by
    refine bind_congr_of_forall_mem_support _ fun z zMember => ?_
    apply PqxdhDeploymentKemTransfer.map_support_congr
    intro outcome outcomeMember
    have settled := PqxdhDeploymentIdealKeymatch.run_settled setup codec route checks t p created (next w.1.1.1.1)
      (mergeXL (startL t snap copies joint log raw w)) (by show t.accept < t.accept + 1; omega) z zMember
    have tail := PqxdhDeploymentIdealLaterBranch.laterTail_marks setup codec checks created second after z.1 z.2 outcome
      outcomeMember
    show decision _ (PqxdhDeploymentIdealLaterCut.markedL outcome) = decision _ w.1.1.1.1.isSome
    rw [tail, settled]
    exact congrArg _ mark
  rw [marked, ← PqxdhDeploymentIdealLaterMid.compile_simulationMidL setup codec route checks t p created phase1 phase2
    (next w.1.1.1.1) _ (good w member), bind_map_left]
  have run := PqxdhDeploymentIdealLaterMid.compiled_run setup codec route checks t p created (next w.1.1.1.1)
    (startL t snap copies joint log raw w)
  have rhs : (simulateQ (sourceMidL setup codec route checks t p created)
      (PqxdhDeploymentIdealLaterBranch.compiledNextL setup codec route second raw next (snap, copies)
        w.1.1.1.1)).run (startL t snap copies joint log raw w).2 =
      (simulateQ (compiledMidL setup codec route checks t p created) (next w.1.1.1.1)).run
        (startL t snap copies joint log raw w) >>= fun r =>
          (simulateQ (sourceMidL setup codec route checks t p created)
            (PqxdhDeploymentIdealLaterCut.restOf setup codec route second (r.1, r.2.1))).run r.2.2 := by
    unfold PqxdhDeploymentIdealLaterBranch.compiledNextL
    rw [simulateQ_bind, StateT.run_bind]
    refine Eq.trans (congrArg (fun x => x >>= fun r : ((X × PqxdhDeploymentSecrecy.Ledger) × (Snap × Local)) ×
      MidL KemSK => (simulateQ (sourceMidL setup codec route checks t p created)
        (PqxdhDeploymentIdealLaterCut.restOf setup codec route second r.1)).run r.2) run) ?_
    rw [bind_map_left]
  rw [rhs, map_bind]
  refine bind_congr_of_forall_mem_support _ fun r rMember => ?_
  have goodR : GoodMidL setup codec t r.2 := PqxdhDeploymentIdealSlots.simulateQ_keeps
    (compiledMidL setup codec route checks t p created) (GoodMidL setup codec t)
    (fun query state holds result supported => PqxdhDeploymentIdealLaterMid.goodMidL_step setup codec route checks t p
      created phase1 phase2 query state holds result supported) (next w.1.1.1.1) _ (good w member) r rMember
  have slotR := slot w member r rMember
  obtain ⟨result, ⟨snap', copies'⟩, m', log'⟩ := r
  exact PqxdhDeploymentIdealLaterMid.laterTail_middle setup codec route checks t p created phase1 phase2
    (fun outcome _ => decision outcome w.1.1.1.1.isSome) second after result snap' copies' m' log' goodR.1 slotR

end CE

/-! ### The decisions on the merge image -/

section Decision
open PqxdhDeploymentInterface (Budget)
open PqxdhDeploymentKemTransfer (Observed)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)

/-- Item 2's tagged decision of the compiled LQ-F program and the later decision together with the mark agree on the merge image: both read the event and the designation on the post-run output, the ledger and the produced frames of the local copies, and whether the selected accept returned a session. -/
theorem decision_mergeL {A Out : Type} (budget : Budget) (event : Observed Out → Bool)
    (claim : Observed Out → Option PqxdhDeploymentInterface.Handle) (g : Fin budget.accept × Fin budget.capacity)
    (created : PqxdhLiveServerConstruction.Created Unit) (raw : Pqxdh.Bytes) (answer : Option ℕ) (after : A)
    (result : (Out × (PqxdhDeploymentSecrecy.Ledger × (Snap × Local))) × MidL KemSK) :
    PqxdhRegistrationJointAcceptCutTag.decideTag
        (PqxdhDeploymentLaterServerTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (result.1, some (raw, answer)) =
      PqxdhDeploymentIdealLaterBranch.markedDecisionL setup codec budget event claim g
        (some (PqxdhRegistrationJointServerBirth.encode created, result.1.1, (result.1.2.1, (result.1.2.2.1,
          (merge result.1.2.2.2 (PqxdhRegistrationJointSchedule.source result.2.1.joint), result.2.2)))), after)
        answer.isSome := by
  rcases answer with _ | session
  · simp [PqxdhRegistrationJointAcceptCutTag.decideTag, PqxdhRegistrationJointAcceptCutTag.accepted,
      PqxdhDeploymentIdealLaterBranch.markedDecisionL]
  · have produced : (merge result.1.2.2.2 (PqxdhRegistrationJointSchedule.source result.2.1.joint)).produced =
        result.1.2.2.2.produced := rfl
    simp only [PqxdhRegistrationJointAcceptCutTag.decideTag, PqxdhRegistrationJointAcceptCutTag.accepted,
      PqxdhDeploymentIdealLaterBranch.markedDecisionL, PqxdhDeploymentLaterServerTransfer.decision,
      PqxdhDeploymentLaterServerTransfer.observeCompiled, PqxdhDeploymentLaterServerTransfer.happens,
      PqxdhDeploymentLaterServerTransfer.designated, PqxdhDeploymentLaterServerTransfer.observeGame,
      Option.isSome_some, Bool.and_true, produced, Option.map_some, Option.any_some, Option.bind_some]
    cases event (result.1.1, result.1.2.1, result.1.2.2.2.produced) <;> simp
    exact decide_eq_decide.mpr Iff.rfl

end Decision

/-! ### Bounds of the logged continuation -/

section Bounds
open PqxdhDeploymentLaterCompile (terminal)
open PqxdhDeploymentIdealLaterSteps (AllowedL CostlyL)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- An embedded source14 program has the bounds of the program on the embedded requests. -/
theorem embed_bound {α : Type} (P : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain → Prop) [DecidablePred P]
    (work : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) α) (n : ℕ)
    (bound : work.IsQueryBoundP (fun query => P (.inl query)) n) : (simulateQ embed work).IsQueryBoundP P n := by
  induction work using OracleComp.inductionOn generalizing n with
  | pure value => simp only [simulateQ_pure, isQueryBoundP_pure]
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bound
      simp only [simulateQ_bind, simulateQ_spec_query, embed]
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨bound.1, fun reply => ih reply _ (bound.2 reply)⟩

/-- The post part of the compiled LQ-F program issues no request of a source kind whose compile cost is zero for the coin, HMAC and BLAKE2b commands (`PqxdhDeploymentIdealLaterMid.post_zero` for every source kind). -/
theorem post_zeroK {Out : Type} (kind : PqxdhRegistrationJointRevealCosts.SourceKind) (coins : PqxdhDeploymentCompileBudget.cost kind 0 = 0)
    (hmac : PqxdhDeploymentCompileBudget.cost kind 6 = 0) (hash : PqxdhDeploymentCompileBudget.cost kind 7 = 0)
    (adversary : OracleComp PostSpec Out) (copies : Local) :
    ((simulateQ (compileImpl setup codec route) (simulateQ PqxdhDeploymentLater.postEmbed adversary)).run
      copies).IsQueryBoundP (fun request => sourceKind (KemSK := KemSK) request = kind) 0 := by
  rw [← QueryImpl.simulateQ_compose]
  refine PqxdhDeploymentCompileSecrecy.simulate_zero ((compileImpl setup codec route) ∘ₛ PqxdhDeploymentLater.postEmbed)
    _ (fun query state => ?_) _ copies
  rcases query with coin | (⟨key, message⟩ | bytes)
  · simp only [QueryImpl.apply_compose, PqxdhDeploymentLater.postEmbed, simulateQ_spec_query]
    have bound := PqxdhDeploymentCompileBudget.step_bound setup codec route (KemSK := KemSK) kind (.inl coin) state
    rwa [show PqxdhDeploymentCompileBudget.commandKind (.inl coin) = 0 from rfl, coins] at bound
  · simp only [QueryImpl.apply_compose, PqxdhDeploymentLater.postEmbed, simulateQ_spec_query]
    have bound := PqxdhDeploymentCompileBudget.step_bound setup codec route (KemSK := KemSK) kind
      (.inr (.hmac key message)) state
    rwa [show PqxdhDeploymentCompileBudget.commandKind (.inr (.hmac key message)) = 6 from rfl, hmac] at bound
  · simp only [QueryImpl.apply_compose, PqxdhDeploymentLater.postEmbed, simulateQ_spec_query]
    have bound := PqxdhDeploymentCompileBudget.step_bound setup codec route (KemSK := KemSK) kind
      (.inr (.hash bytes)) state
    rwa [show PqxdhDeploymentCompileBudget.commandKind (.inr (.hash bytes)) = 7 from rfl, hash] at bound

/-- The rest of the compiled LQ-F program (`PqxdhDeploymentIdealLaterCut.restOf`) issues no request of a class that its terminal reads and post part avoid and that is not the Server read. -/
theorem restOf_bound {X Out : Type} (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out)
    (run : (X × PqxdhDeploymentSecrecy.Ledger) × (Snap × Local))
    (P : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain → Prop) [DecidablePred P]
    (terminalFree : ∀ (snap : Snap) (indices : List ℕ),
      (terminal (KemSK := KemSK) snap indices).IsQueryBoundP (fun query => P (.inl query)) 0)
    (readFree : ¬ P (.inr ()))
    (postFree : ∀ (adversary : OracleComp PostSpec Out) (copies : Local),
      ((simulateQ (compileImpl setup codec route) (simulateQ PqxdhDeploymentLater.postEmbed adversary)).run
        copies).IsQueryBoundP (fun query => P (.inl query)) 0) :
    (PqxdhDeploymentIdealLaterCut.restOf setup codec route second run).IsQueryBoundP P 0 := by
  unfold PqxdhDeploymentIdealLaterCut.restOf
  refine isQueryBoundP_bind (n := 0) (m := 0) (embed_bound _ _ _ (terminalFree _ _)) fun beacons _ => ?_
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl readFree, fun server => ?_⟩
  simp only [readFree, ite_false]
  exact isQueryBoundP_bind (n := 0) (m := 0) (embed_bound _ _ _ (postFree _ _)) fun post _ => isQueryBoundP_pure _ _ _

/-- The rest of the compiled LQ-F program reads no KEM field. -/
theorem restOf_allowed {X Out : Type} (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out)
    (run : (X × PqxdhDeploymentSecrecy.Ledger) × (Snap × Local)) :
    (PqxdhDeploymentIdealLaterCut.restOf setup codec route second run).IsQueryBoundP
      (fun query => ¬ AllowedL (KemSK := KemSK) query) 0 :=
  restOf_bound setup codec route second run _
    (fun snap indices => (isQueryBoundP_congr_pred (p := fun query => ¬ AllowedL (KemSK := KemSK) (.inl query))
      (p' := fun query => sourceKind (KemSK := KemSK) query = .inr 1) fun query => by simp [AllowedL]).mpr (by
      simpa [PqxdhDeploymentLaterCompile.readCost, PqxdhDeploymentCompileBudget.unit] using
        PqxdhDeploymentLaterCompile.terminal_bound (KemSK := KemSK) (.inr 1) snap indices))
    (by simp [AllowedL])
    (fun adversary copies => (isQueryBoundP_congr_pred (p := fun query => ¬ AllowedL (KemSK := KemSK) (.inl query))
      (p' := fun query => sourceKind (KemSK := KemSK) query = .inr 1) fun query => by simp [AllowedL]).mpr
      (post_zeroK setup codec route (.inr 1) (by decide) (by decide) (by decide) adversary copies))

/-- The rest of the compiled LQ-F program creates nothing. -/
theorem restOf_costly {X Out : Type} (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out)
    (run : (X × PqxdhDeploymentSecrecy.Ledger) × (Snap × Local)) :
    (PqxdhDeploymentIdealLaterCut.restOf setup codec route second run).IsQueryBoundP (CostlyL (KemSK := KemSK)) 0 :=
  restOf_bound setup codec route second run _
    (fun snap indices => (isQueryBoundP_congr_pred (p := fun query => CostlyL (KemSK := KemSK) (.inl query))
      (p' := fun query => sourceKind (KemSK := KemSK) query = .inl 1) fun query => by
      simp [CostlyL, PqxdhDeploymentIdealPostInvariant.Costly]).mpr (by
      simpa [PqxdhDeploymentLaterCompile.readCost, PqxdhDeploymentCompileBudget.unit] using
        PqxdhDeploymentLaterCompile.terminal_bound (KemSK := KemSK) (.inl 1) snap indices))
    (by simp [CostlyL])
    (fun adversary copies => (isQueryBoundP_congr_pred (p := fun query => CostlyL (KemSK := KemSK) (.inl query))
      (p' := fun query => sourceKind (KemSK := KemSK) query = .inl 1) fun query => by
      simp [CostlyL, PqxdhDeploymentIdealPostInvariant.Costly]).mpr
      (post_zeroK setup codec route (.inl 1) (by decide) (by decide) (by decide) adversary copies))

end Bounds

/-! ### The start of the logged middle run after the selected accept -/

section Start
open PqxdhDeploymentIdealLaterSteps (ItemInvL roomL AllowedL CostlyL)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- The steps after encapsulation return the logged scalar they are given as the accept's logged entry. -/
theorem acceptAfter_logged (seed : PqxdhJointIdentity.IdentitySeed) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes) (consumed : List Pqxdh.Bytes)
    (logged : Option PqxdhJointGapDh.ScalarBytes) (native : PqxdhServerAuthNative.NativeState KemSK)
    (r : PqxdhDeploymentIdealSteps.AcceptOut × PqxdhServerAuthNative.NativeState KemSK)
    (member : r ∈ support ((PqxdhDeploymentIdealActive.acceptAfter setup codec checks seed challenge value ephemeral
      consumed logged).run native)) :
    r.1.1.2 = logged := by
  change r ∈ support (PqxdhDeploymentIdealSteps.liftS _ >>= _) at member
  rw [mem_support_bind_iff] at member
  obtain ⟨prepared, -, member⟩ := member
  rw [mem_support_bind_iff] at member
  obtain ⟨answer, -, member⟩ := member
  rw [support_pure, Set.mem_singleton_iff] at member
  subst member
  rfl

/-- `GoodMidL` holds after the selected accept: CE-3's invariant at the cut survives the steps after encapsulation, which have the footprint of a raw accept (`PqxdhDeploymentIdealPostGood.acceptAfter_footprint`, `good_of_accept`, `identityOf_verified`), and the accept counter is one past the selected ordinal (CE-11b's `PqxdhDeploymentIdealPostGood.middleStart`). -/
theorem start_goodL (raw : Pqxdh.Bytes) (value : PqxdhServerRootPreparation.Verified Reader)
    (verified : PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value) (snap : Snap)
    (copies : Local) (joint : PqxdhRegistrationJointSchedule.State KemSK) (log : Log)
    (good : Good setup codec copies (PqxdhRegistrationJointSchedule.source joint))
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes) (consumed : List Pqxdh.Bytes)
    (logged : Option PqxdhJointGapDh.ScalarBytes) (w : AcceptRun KemSK)
    (member : w ∈ support ((simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
      ((PqxdhDeploymentIdealActive.acceptAfter setup codec checks created.seed p.challenge value ephemeral consumed
        logged).run joint.shared)).run (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial))) :
    GoodMidL setup codec t (startL t snap copies joint log raw w) := by
  refine ⟨?_, Nat.lt_succ_self _⟩
  obtain ⟨server, keyId, sessions, others, rejected, accepted⟩ :=
    PqxdhDeploymentIdealPostGood.acceptAfter_footprint setup codec checks created.seed p.challenge value ephemeral
      consumed logged joint.shared _ w member
  exact PqxdhDeploymentIdealPostGood.good_of_accept setup codec raw copies (PqxdhRegistrationJointSchedule.source joint)
    ⟨w.1.2, (PqxdhRegistrationJointSchedule.source joint).owners⟩ good w.1.1.1.1 rfl server keyId sessions others rejected
    (fun session found => by
      obtain ⟨same, token, stored, identity⟩ := accepted session found
      exact ⟨same, token, stored, by
        rw [identity]
        exact PqxdhDeploymentIdealPostGood.identityOf_verified setup codec checks raw value verified⟩)

/-- Item 2's invariant holds after the selected accept (`PqxdhDeploymentIdealPostItemRun.itemInv_after`). -/
theorem start_itemL (raw : Pqxdh.Bytes) (value : PqxdhServerRootPreparation.Verified Reader) (snap : Snap)
    (copies : Local) (joint : PqxdhRegistrationJointSchedule.State KemSK) (log : Log)
    (owned : PqxdhDeploymentIdealPoolSource.PoolOwned created.seed created.server.server.metadata.identityIndex joint)
    (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) joint.pool.2)
    (indexed : PqxdhDeploymentIdealCut.PoolIndexed joint)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes) (consumed : List Pqxdh.Bytes)
    (logged : Option PqxdhJointGapDh.ScalarBytes) (w : AcceptRun KemSK)
    (member : w ∈ support ((simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
      ((PqxdhDeploymentIdealActive.acceptAfter setup codec checks created.seed p.challenge value ephemeral consumed
        logged).run joint.shared)).run (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial))) :
    ItemInvL created t p (startL t snap copies joint log raw w).2 := by
  have produced : w.1 ∈ support ((PqxdhDeploymentIdealActive.acceptAfter setup codec checks created.seed p.challenge value
      ephemeral consumed logged).run joint.shared) := by
    apply OracleComp.support_simulateQ_run'_subset
      (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService) _
      (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial)
    rw [StateT.run'_eq, support_map]
    exact ⟨w, member, rfl⟩
  have active := (PqxdhDeploymentIdealPostMark.acceptAfter_mark setup codec checks created.seed p.challenge value ephemeral
    consumed logged joint.shared w.1 produced).1
  obtain ⟨good, stored⟩ := PqxdhDeploymentIdealPostItemRun.acceptAfter_keeps setup codec checks p created.seed value
    ephemeral consumed logged joint.shared _ PqxdhRegistrationJointKemSecondEntry.slotGood_empty (by decide) w member
  exact PqxdhDeploymentIdealPostItemRun.itemInv_after t p created joint owned prefixed indexed w active good stored

/-- On every state reached by the compiled run part over the logged middle source handler from a state with item 2's invariant, the Server's identity slot holds its seed, when the run part reads no KEM field and creates at most the room's number of KEM keys (item 2's invariant is kept, `PqxdhDeploymentIdealLaterSteps.simulate_keeps` with `keep_allL`). -/
theorem run_slotL {X : Type} (work : OracleComp Spec X) (state : (Snap × Local) × MidL KemSK)
    (holds : ItemInvL created t p state.2) (budget : ℕ)
    (kemFree : ((simulateQ (compileSnapImpl setup codec route) work).run state.1).IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = .inr 1) 0)
    (createBound : ((simulateQ (compileSnapImpl setup codec route) work).run state.1).IsQueryBoundP
      (fun query => sourceKind (KemSK := KemSK) query = .inl 1) budget)
    (fits : budget ≤ roomL t p state.2) :
    ∀ r ∈ support ((simulateQ (compiledMidL setup codec route checks t p created) work).run state),
      r.2.2.1.joint.pool.1.seeds[created.server.server.metadata.identityIndex]? = some created.seed := by
  intro r member
  have reached : ((r.1, r.2.1), r.2.2) ∈ support ((simulateQ (sourceMidL setup codec route checks t p created)
      (simulateQ embed ((simulateQ (compileSnapImpl setup codec route) work).run state.1))).run state.2) := by
    rw [PqxdhDeploymentIdealLaterMid.compiled_run, support_map]
    exact ⟨r, member, rfl⟩
  have kept := PqxdhDeploymentIdealLaterSteps.simulate_keeps (sourceMidL setup codec route checks t p created)
    (ItemInvL created t p) AllowedL CostlyL (roomL t p)
    (fun query state holds _ fits => PqxdhDeploymentIdealLaterSteps.keep_allL setup codec route checks t p created query
      state holds fits)
    _ (embed_bound _ _ _ ((isQueryBoundP_congr_pred (p := fun query => ¬ AllowedL (KemSK := KemSK) (.inl query))
      (p' := fun query => sourceKind (KemSK := KemSK) query = .inr 1) fun query => by simp [AllowedL]).mpr kemFree))
    budget (embed_bound _ _ _ ((isQueryBoundP_congr_pred (p := fun query => CostlyL (KemSK := KemSK) (.inl query))
      (p' := fun query => sourceKind (KemSK := KemSK) query = .inl 1) fun query => by
        simp [CostlyL, PqxdhDeploymentIdealPostInvariant.Costly]).mpr createBound))
    state.2 fits holds _ reached
  exact kept.owned.1.2

end Start

/-! ### The active branch -/

section Active
open PqxdhDeploymentInterface (Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentKemTransfer (Observed)
open LazyOracleDiscard (LawEq)
open PqxdhDeploymentIdealLaterSteps (AllowedL CostlyL)
variable {X : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (checks : Checks)

/-- The active branch of the later second compile lemma (`PqxdhDeploymentIdealLaterBranch.ActiveBranchL`) at every draw of the challenger, under the approved Phase 1 and Phase 2 read-back contracts. Item 2's side is the logged middle run (`PqxdhDeploymentIdealLaterSteps.itemPost_middleL`, with the logged continuation's bounds from the relation at the cut and `restOf_allowed`, `restOf_costly`), the CE side is a function of the same run (`activeCE_middleL`, with `start_goodL` and `run_slotL`), the logged entries agree (`acceptAfter_logged`, `PqxdhDeploymentLaterServerSource.beforeLogged_some`), and the two decisions agree on the merge image (`decision_mergeL`). -/
theorem active_branchL {A Out : Type} (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (budget : Budget)
    (event : Observed Out → Bool) (claim : Observed Out → Option PqxdhDeploymentInterface.Handle)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) (p : Params KemSK budget.create) :
    PqxdhDeploymentIdealLaterBranch.ActiveBranchL (Reader := Reader) setup codec route checks ensureInit bounds mode first
      second budget event claim g runtime p := by
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
  have loggedEq : pre.1.2 = some ephemeral.secret := by
    have inner : pre.1 ∈ support (PqxdhDeploymentLaterServerSource.beforeLogged
        (Shared := PqxdhBeaconPhase2Preparation.Word32) value) := by
      apply OracleComp.support_simulateQ_run'_subset
        (PqxdhDeploymentIdealSteps.prefixNative setup codec checks created.seed) _
        reached.2.1.shared.2.server.consumed
      rw [StateT.run'_eq, support_map]
      exact ⟨pre, preMember, rfl⟩
    exact PqxdhDeploymentLaterServerSource.beforeLogged_some value pre.1 ephemeral inner found
  have cutEq : PqxdhDeploymentIdealLaterCut.compileCutSnap setup codec route reached.1 =
      .pending raw (fun answer => (simulateQ (compileSnapImpl setup codec route) (next answer)).run
        (reached.1.2.1, copiesAfter reached.1.2.2 raw answer)) := by
    rcases reached with ⟨⟨cut, snap, copies⟩, state⟩
    simp only at pending
    subst pending
    rfl
  have residual := related.residual raw _ cutEq
  have caps := PqxdhDeploymentIdealLaterBranch.runBudget_caps bounds budget
  have kemFree : ∀ answer, ((simulateQ (compileSnapImpl setup codec route) (next answer)).run
      (reached.1.2.1, copiesAfter reached.1.2.2 raw answer)).IsQueryBoundP
        (fun query => sourceKind (KemSK := KemSK) query = .inr 1) 0 := by
    intro answer
    have bound := residual answer (.inr 1)
    rwa [Function.update_of_ne (by simp), caps.2.1] at bound
  have createBound : ∀ answer, ((simulateQ (compileSnapImpl setup codec route) (next answer)).run
      (reached.1.2.1, copiesAfter reached.1.2.2 raw answer)).IsQueryBoundP
        (fun query => sourceKind (KemSK := KemSK) query = .inl 1) (budget.create - reached.2.1.pool.2.keys.length) := by
    intro answer
    have bound := residual answer (.inl 1)
    rwa [Function.update_self, caps.2.2] at bound
  have onlyAllowed : ∀ answer, (PqxdhDeploymentIdealLaterBranch.compiledNextL setup codec route second raw next
      reached.1.2 answer).IsQueryBoundP (fun query => ¬ AllowedL (KemSK := KemSK) query) 0 := fun answer =>
    isQueryBoundP_bind (n := 0) (m := 0) (embed_bound _ _ _ ((isQueryBoundP_congr_pred
      (p := fun query => ¬ AllowedL (KemSK := KemSK) (.inl query))
      (p' := fun query => sourceKind (KemSK := KemSK) query = .inr 1) fun query => by simp [AllowedL]).mpr
        (kemFree answer))) fun run _ => restOf_allowed setup codec route second run
  have bounded : ∀ answer, (PqxdhDeploymentIdealLaterBranch.compiledNextL setup codec route second raw next
      reached.1.2 answer).IsQueryBoundP (CostlyL (KemSK := KemSK)) (budget.create - reached.2.1.pool.2.keys.length) :=
    fun answer => isQueryBoundP_bind (m := 0) (embed_bound _ _ _ ((isQueryBoundP_congr_pred
      (p := fun query => CostlyL (KemSK := KemSK) (.inl query))
      (p' := fun query => sourceKind (KemSK := KemSK) query = .inl 1) fun query => by
        simp [CostlyL, PqxdhDeploymentIdealPostInvariant.Costly]).mpr (createBound answer)))
      fun run _ => restOf_costly setup codec route second run
  have fits : budget.create - reached.2.1.pool.2.keys.length ≤
      (p.pool (Target.ofCE budget g)).length - reached.2.1.pool.2.keys.length := by
    rw [PqxdhDeploymentIdealParams.pool_length]
    omega
  rw [PqxdhDeploymentIdealLaterSteps.itemPost_middleL setup codec route checks (Target.ofCE budget g) p
      (PqxdhDeploymentLaterServerTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
      created identity raw value matched ephemeral pre.2 pre.1.2 reached.2.1 reached.2.2 related.owned related.prefixed
      related.indexed _ onlyAllowed _ bounded fits born.2.2,
    activeCE_middleL setup codec route checks (Target.ofCE budget g) p created phase1 phase2 _ second born.2.2
      reached.1.2.1 reached.1.2.2 reached.2.1 reached.2.2 raw next value ephemeral pre.2 pre.1.2
      (fun w member => start_goodL setup codec checks (Target.ofCE budget g) p created raw value verified reached.1.2.1
        reached.1.2.2 reached.2.1 reached.2.2 related.good ephemeral pre.2 pre.1.2 w member)
      (fun w member => run_slotL setup codec route checks (Target.ofCE budget g) p created (next w.1.1.1.1)
        (startL (Target.ofCE budget g) reached.1.2.1 reached.1.2.2 reached.2.1 reached.2.2 raw w)
        (start_itemL setup codec checks (Target.ofCE budget g) p created raw value reached.1.2.1 reached.1.2.2
          reached.2.1 reached.2.2 related.owned related.prefixed related.indexed ephemeral pre.2 pre.1.2 w member)
        _ (kemFree w.1.1.1.1) (createBound w.1.1.1.1) fits)]
  refine bind_congr_of_forall_mem_support _ fun w member => ?_
  have produced : w.1 ∈ support ((PqxdhDeploymentIdealActive.acceptAfter setup codec checks created.seed p.challenge value
      ephemeral pre.2 pre.1.2).run reached.2.1.shared) := by
    apply OracleComp.support_simulateQ_run'_subset
      (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService) _
      (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial)
    rw [StateT.run'_eq, support_map]
    exact ⟨w, member, rfl⟩
  have entry : w.1.1.1.2 = some ephemeral.secret := by
    rw [acceptAfter_logged setup codec checks created.seed p.challenge value ephemeral pre.2 pre.1.2 reached.2.1.shared w.1
      produced, loggedEq]
  show _ = _ <$> (simulateQ (sourceMidL setup codec route checks (Target.ofCE budget g) p created)
    (PqxdhDeploymentIdealLaterBranch.compiledNextL setup codec route second raw next reached.1.2 w.1.1.1.1)).run
      (afterSelected (Target.ofCE budget g) reached.2.1 w, reached.2.2 ++ [w.1.1.1.2])
  rw [entry]
  unfold PqxdhDeploymentLaterServerCut.tagged
  rw [simulateQ_map, StateT.run_map, Functor.map_map]
  refine congrArg (fun f => f <$> _) (funext fun result => ?_)
  exact decision_mergeL setup codec budget event claim g created raw w.1.1.1.1 born.2.2 result

end Active

end BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPost

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPost.activeCE_middleL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPost.activeCE_middleL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPost.decision_mergeL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPost.decision_mergeL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPost.embed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPost.embed_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPost.post_zeroK' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPost.post_zeroK

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPost.restOf_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPost.restOf_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPost.restOf_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPost.restOf_allowed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPost.restOf_costly' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPost.restOf_costly

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPost.acceptAfter_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPost.acceptAfter_logged

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPost.start_goodL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPost.start_goodL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPost.start_itemL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPost.start_itemL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPost.run_slotL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPost.run_slotL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPost.active_branchL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterPost.active_branchL

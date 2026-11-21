-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawSelectedAccept
import BeaconcryptCore.Computational.CborRawMarkedPrefix

/-! Selected and inactive branches of the initialized raw ideal execution. The final private mark is derived from the actual selected accept, including rejection, and retained by every subsequent native raw command. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawMarkedBranch
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealPostItemRun (afterSelected)
open PqxdhDeploymentIdealCut (cutState)
open CborRawPublicState (Public ofMemory)
open CborRawMiddleSimulation (Native)
open CborRawMiddleMarks (counter marks)
open CborRawSelectedAccept (decorate reject)
open LazyOracleDiscard (LawEq)
variable {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}
section Branch
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)

theorem resume_dead (event : Result × CborRawPostActive.Produced → Bool) (raw : Pqxdh.Bytes)
    (next : Option Nat → OracleComp Spec Result) (state : Public × Native KemSK)
    (selected : counter state = target.accept)
    (inactive : ∀ value, PqxdhRegistrationJointRawSignatures.verified setup (CborRawCompile.sourceCodec wire parse)
      checks raw = some value → value.keys.pqKey ≠ parameters.chosen.1) :
    LawEq (CborRawMarkedPrefix.resume setup wire parse checks target parameters created event (.pending raw next) state)
      (pure false) := by
  unfold CborRawMarkedPrefix.resume CborRawPrefixHandoff.resume CborRawMarkedPrefix.run
  simp only [PqxdhDeploymentIdealCut.finishCE, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
  rw [← map_bind]
  apply PqxdhDeploymentIdealBranch.map_const_lawEq
  intro result supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨accepted, acceptedMember, supported⟩ := supported
  obtain ⟨clock, empty⟩ := CborRawMiddleMarks.accept_inactive setup wire parse checks target parameters created raw
    inactive state selected accepted acceptedMember
  have settled := CborRawMiddleMarks.run_settled setup wire parse checks target parameters created (next accepted.1)
    accepted.2 (by rw [clock]; exact Nat.lt_succ_self _) result supported
  rw [settled, empty]
  exact Bool.and_false _

/-- The accepted-session flag equals the final mark even when later native writes fail or admission refuses a record. -/
theorem active_marked (event : Result × CborRawPostActive.Produced → Bool)
    (memory : CborAdmissionCompiler.Local) (joint : PqxdhRegistrationJointSchedule.State KemSK)
    (raw : Pqxdh.Bytes) (next : Option Nat → OracleComp Spec Result)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (logged : Option PqxdhJointGapDh.ScalarBytes)
    (selected : PqxdhDeploymentIdealPostItemRun.AcceptRun KemSK)
    (supported : selected ∈ support
      ((simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
        ((PqxdhDeploymentIdealActive.acceptAfter setup (CborRawCompile.sourceCodec wire parse) checks created.seed
          parameters.challenge value ephemeral consumed logged).run joint.shared)).run
            (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial))) :
    CborRawMarkedPrefix.run setup wire parse checks target parameters created (next selected.1.1.1.1) event
        (CborRawMiddleSimulation.merge (CborRawCompileCut.logAccept memory raw selected.1.1.1.1)
          (afterSelected target joint selected)) =
      (fun result => event (result.1, result.2.2.base.produced) && selected.1.1.1.1.isSome) <$>
        (simulateQ (CborRawMiddleSimulation.handler setup wire parse checks target parameters created)
          (next selected.1.1.1.1)).run
          (CborRawMiddleSimulation.merge (CborRawCompileCut.logAccept memory raw selected.1.1.1.1)
            (afterSelected target joint selected)) := by
  have produced : selected.1 ∈ support ((PqxdhDeploymentIdealActive.acceptAfter setup
      (CborRawCompile.sourceCodec wire parse) checks created.seed parameters.challenge value ephemeral consumed
        logged).run joint.shared) := by
    apply OracleComp.support_simulateQ_run'_subset
      (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService) _
      (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial)
    rw [StateT.run'_eq, support_map]
    exact ⟨selected, supported, rfl⟩
  have mark := (PqxdhDeploymentIdealPostMark.acceptAfter_mark setup (CborRawCompile.sourceCodec wire parse) checks
    created.seed parameters.challenge value ephemeral consumed logged joint.shared selected.1 produced).2
  apply PqxdhDeploymentKemTransfer.map_support_congr
  intro result member
  have beyond : target.accept < counter (CborRawMiddleSimulation.merge
      (CborRawCompileCut.logAccept memory raw selected.1.1.1.1) (afterSelected target joint selected)) :=
    Nat.lt_succ_self _
  have settled := CborRawMiddleMarks.run_settled setup wire parse checks target parameters created
    (next selected.1.1.1.1) _ beyond result member
  rw [settled]
  change (event (result.1, result.2.2.base.produced) && selected.1.1.2.2.isSome) = _
  rw [mark]

/-- A rejection before encapsulation increments the selected ordinal and leaves the whole continuation unmarked. -/
theorem reject_dead (event : Result × CborRawPostActive.Produced → Bool)
    (publicState : Public) (base : PqxdhDeploymentNative.State KemSK) (raw : Pqxdh.Bytes)
    (next : Option Nat → OracleComp Spec Result) (consumed : List Pqxdh.Bytes)
    (logged : Option PqxdhJointGapDh.ScalarBytes) :
    LawEq ((reject (Reader := Reader) setup target created base consumed logged) >>= fun accepted =>
        CborRawMarkedPrefix.run setup wire parse checks target parameters created (next accepted.1) event
          (decorate publicState raw accepted).2) (pure false) := by
  unfold CborRawMarkedPrefix.run
  rw [← map_bind]
  apply PqxdhDeploymentIdealBranch.map_const_lawEq
  intro result member
  rw [mem_support_bind_iff] at member
  obtain ⟨accepted, acceptedMember, member⟩ := member
  unfold reject at acceptedMember
  rw [support_map] at acceptedMember
  obtain ⟨inner, innerMember, rfl⟩ := acceptedMember
  have produced : inner.1 ∈ support ((PqxdhDeploymentIdealActive.selectedStep (fun state => do
      let value ← PqxdhDeploymentIdealSteps.liftS ((PqxdhRegistrationJointServerAccept.tail (Reader := Reader) setup
        (setup.joint.publicKeys created.seed) state.2 (none, consumed)).run state)
      pure (((value.1, logged), (false, none)), value.2))).run
        (PqxdhDeploymentIdealSlots.detach (cutState target created base))) := by
    apply OracleComp.support_simulateQ_run'_subset
      (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService) _
      ((cutState target created base).backend.2.1, (cutState target created base).backend.1)
    rw [StateT.run'_eq, support_map]
    exact ⟨inner, innerMember, rfl⟩
  unfold PqxdhDeploymentIdealActive.selectedStep at produced
  rw [StateT.run, support_map] at produced
  obtain ⟨rejected, rejectedMember, same⟩ := produced
  dsimp only [StateT.run] at rejectedMember
  rw [mem_support_bind_iff] at rejectedMember
  obtain ⟨_, _, rejectedMember⟩ := rejectedMember
  rw [support_pure, Set.mem_singleton_iff] at rejectedMember
  subst rejectedMember
  have empty : marks (decorate publicState raw
      (inner.1.1, PqxdhDeploymentIdealSlots.attach inner.1.2 inner.2.1 inner.2.2)).2 = none := by rw [← same]; rfl
  have clock : counter (decorate publicState raw
      (inner.1.1, PqxdhDeploymentIdealSlots.attach inner.1.2 inner.2.1 inner.2.2)).2 = target.accept + 1 := by
    rw [← same]
    rfl
  have settled := CborRawMiddleMarks.run_settled setup wire parse checks target parameters created (next inner.1.1) _
    (by rw [clock]; exact Nat.lt_succ_self _) result member
  rw [settled, empty]
  exact Bool.and_false _

end Branch
end BeaconcryptCore.Computational.CborRawMarkedBranch

/-- info: 'BeaconcryptCore.Computational.CborRawMarkedBranch.resume_dead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMarkedBranch.resume_dead
/-- info: 'BeaconcryptCore.Computational.CborRawMarkedBranch.active_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMarkedBranch.active_marked
/-- info: 'BeaconcryptCore.Computational.CborRawMarkedBranch.reject_dead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMarkedBranch.reject_dead

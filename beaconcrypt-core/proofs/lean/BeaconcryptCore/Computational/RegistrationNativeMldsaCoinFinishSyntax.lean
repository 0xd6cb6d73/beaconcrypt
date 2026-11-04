-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconRecordExecutor

/-! The actual initial receive-loop controller reaches at most one shared commitment request. Its arbitrary-length KDF prefix has no hash-class charge. The proof follows the existing extracted continuation rank, including absent replies, mismatches, failed getters and rejected AEAD admission. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCoinFinishSyntax
open RegistrationBeaconRecordExecutor
open RegistrationRecordPrimitives (Spec)
variable {Input : Type}

def IsHash : Spec.Domain → Prop
  | .hash _ => True
  | _ => False
instance : DecidablePred IsHash := fun query => by
  cases query <;> first | exact instDecidableFalse | exact instDecidableTrue

def hashBudget : registration.BeaconInitialOpen → Nat
  | .AeadRequested _ => 0
  | _ => 1

attribute [local irreducible] registration.BeaconRecordKdf.resume registration.BeaconRecordCommitment.resume

private theorem continue_bound (action : RustM Input)
    (next : Input → OracleComp Spec (RustM Result)) (count : Nat)
    (bounded : ∀ value, (next value).IsQueryBoundP IsHash count) :
    (continueWith action next).IsQueryBoundP IsHash count := by
  cases action with
  | ok value => exact bounded value
  | fail error | div => trivial

private theorem aead (pending : registration.BeaconRecordAead) :
    (program (.AeadRequested pending)).IsQueryBoundP IsHash 0 := by
  rw [program.eq_def]
  apply continue_bound
  intro request
  cases request with
  | none => trivial
  | some request =>
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inl (fun impossible => impossible.elim), fun _ => by trivial⟩

/-- Source KDF iterations preserve the sole commitment slot, and the commitment consumes it before AEAD. -/
theorem phase (initial : registration.BeaconInitialOpen) :
    (program initial).IsQueryBoundP IsHash (hashBudget initial) := by
  cases initial with
  | AeadRequested pending => exact aead pending
  | KdfRequested pending =>
      rw [program.eq_def]
      apply continue_bound
      intro request
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inl (fun impossible => impossible.elim), fun reply => ?_⟩
      cases actual : pending.resume reply with
      | fail error | div => trivial
      | ok result => cases result with
        | Err aborted => trivial
        | Ok next => exact (phase next).mono (by cases next <;> simp [hashBudget, IsHash])
  | CommitmentRequested pending =>
      rw [program.eq_def]
      apply continue_bound
      intro transcript
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inr Nat.zero_lt_one, fun digest => ?_⟩
      apply continue_bound
      intro supplied
      cases actual : pending.resume (commitmentMatches digest supplied) with
      | fail error | div => trivial
      | ok result => cases result with
        | Err aborted => trivial
        | Ok next =>
          have lower := commitment_rank pending (commitmentMatches digest supplied) next actual
          cases next with
          | AeadRequested selected => exact aead selected
          | KdfRequested selected => simp only [rank] at lower; omega
          | CommitmentRequested selected => simp only [rank] at lower; omega
termination_by rank initial
decreasing_by exact kdf_rank pending reply next actual

private theorem initial (pending : registration.BeaconInitialKdf) :
    (fromInitial pending).IsQueryBoundP IsHash 1 := by
  unfold fromInitial
  apply continue_bound
  intro request
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl (fun impossible => impossible.elim), fun reply => ?_⟩
  cases pending.resume reply with
  | fail error | div => trivial
  | ok result => cases result with
    | Err aborted => trivial
    | Ok next => exact (phase next).mono (by cases next <;> simp [hashBudget, IsHash])

/-- Every actual first-record receive controller has at most one shared-hash request, independent of its source KDF-loop length. -/
theorem begin_bound (agreement : agreement.BeaconAgreement) : (begin agreement).IsQueryBoundP IsHash 1 := by
  unfold begin
  exact continue_bound _ _ _ initial
end BeaconcryptCore.Computational.RegistrationNativeMldsaCoinFinishSyntax

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinFinishSyntax.phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinFinishSyntax.phase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinFinishSyntax.begin_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinFinishSyntax.begin_bound

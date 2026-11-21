-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationRecords

/-! The actual Server commitment transcript is a mutable source lens. Any replacement, including the deployed erased transcript after a failed hash, leaves the actual next Core continuation unchanged. This concerns source dataflow and returned capabilities; it makes no physical memory-erasure or primitive-hash security claim. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.AdapterServerCommitmentLens

def replace (pending : registration.ServerRecordCommitment) (transcript : commitment.CommitmentTranscript) :
    registration.ServerRecordCommitment :=
  { pending with pending := { pending.pending with transcript := transcript } }

theorem getter (pending : registration.ServerRecordCommitment) :
    pending.transcript_mut = .ok (pending.pending.transcript, replace pending) := rfl

theorem resume_replace (pending : registration.ServerRecordCommitment)
    (transcript : commitment.CommitmentTranscript) (reply : core.option.Option (Std.Array U8 64#usize)) :
    (replace pending transcript).resume reply = pending.resume reply := by
  rfl

theorem replacement_retains (pending : registration.ServerRecordCommitment)
    (transcript : commitment.CommitmentTranscript) :
    (replace pending transcript).state = pending.state ∧
      (replace pending transcript).pending.seal = pending.pending.seal ∧
      (replace pending transcript).pending.ciphertext = pending.pending.ciphertext ∧
      (replace pending transcript).pending.tag = pending.pending.tag :=
  ⟨rfl, rfl, rfl, rfl⟩

end BeaconcryptCore.Refinement.AdapterServerCommitmentLens

/-- info: 'BeaconcryptCore.Refinement.AdapterServerCommitmentLens.getter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterServerCommitmentLens.getter
/-- info: 'BeaconcryptCore.Refinement.AdapterServerCommitmentLens.resume_replace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterServerCommitmentLens.resume_replace
/-- info: 'BeaconcryptCore.Refinement.AdapterServerCommitmentLens.replacement_retains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterServerCommitmentLens.replacement_retains

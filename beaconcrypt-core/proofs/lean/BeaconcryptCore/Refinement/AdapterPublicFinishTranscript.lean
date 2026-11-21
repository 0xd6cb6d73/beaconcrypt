-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicFinishReady
/-! The actual first-open commitment transcript is borrowed and written back before comparison. Replacing that consumed transcript does not change the retained supplied commitment or subsequent Core continuation, for either comparison result. These exact source field equations justify retaining the mutation while projecting the later record result. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
namespace BeaconcryptCore.Refinement.AdapterPublicFinishTranscript

def replaced (pending : registration.BeaconRecordCommitment) (transcript : commitment.CommitmentTranscript) :
    registration.BeaconRecordCommitment :=
  { pending with pending := { pending := { pending.pending.pending with transcript := transcript } } }

theorem borrowed (pending : registration.BeaconRecordCommitment) :
    pending.transcript_mut = .ok (pending.pending.pending.transcript, replaced pending) := rfl

theorem supplied (pending : registration.BeaconRecordCommitment) (transcript : commitment.CommitmentTranscript) :
    (replaced pending transcript).supplied_commitment = pending.supplied_commitment := rfl

theorem resume (pending : registration.BeaconRecordCommitment) (transcript : commitment.CommitmentTranscript) (matched : Bool) :
    (replaced pending transcript).resume matched = pending.resume matched := by
  cases matched <;> rfl
end BeaconcryptCore.Refinement.AdapterPublicFinishTranscript

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishTranscript.borrowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishTranscript.borrowed

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishTranscript.supplied' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishTranscript.supplied

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishTranscript.resume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishTranscript.resume

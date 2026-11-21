-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationRecords

/-! Finite initial-record reachability is generated only by actual extracted registration calls. Terminal errors have no outgoing edge. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
open BeaconcryptCore.Refinement.RegistrationRecords

set_option autoImplicit false

namespace BeaconcryptCore.Refinement.RegistrationReachability

/-- A live phase is reachable only after the actual constructor or retained continuation returns it. -/
inductive BeaconRecordReachable (initial : registration.BeaconInitialKdf) : registration.BeaconInitialOpen → Prop
  | start (response : core.option.Option pqxdh.concrete.InitialRatchetKdfResponse)
      (phase : registration.BeaconInitialOpen)
      (actual : initial.resume response = ok (.Ok phase)) :
      BeaconRecordReachable initial phase
  | kdf (pending : registration.BeaconRecordKdf)
      (response : core.option.Option ratchet.RatchetKdfResponse) (phase : registration.BeaconInitialOpen)
      (prior : BeaconRecordReachable initial (.KdfRequested pending))
      (actual : pending.resume response = ok (.Ok phase)) :
      BeaconRecordReachable initial phase
  | commitment (pending : registration.BeaconRecordCommitment) (matched : Bool)
      (phase : registration.BeaconInitialOpen)
      (prior : BeaconRecordReachable initial (.CommitmentRequested pending))
      (actual : pending.resume matched = ok (.Ok phase)) :
      BeaconRecordReachable initial phase
  | transcript (pending : registration.BeaconRecordCommitment)
      (current : commitment.CommitmentTranscript)
      (put : commitment.CommitmentTranscript → registration.BeaconRecordCommitment)
      (replacement : commitment.CommitmentTranscript)
      (prior : BeaconRecordReachable initial (.CommitmentRequested pending))
      (actual : pending.transcript_mut = ok (current, put)) :
      BeaconRecordReachable initial (.CommitmentRequested (put replacement))

/-- A proved actual operation outcome transfers its invariant to the exact successful returned phase. -/
theorem metadata_of_success (expected : agreement.BeaconAgreement)
    (call : RustM (core.result.Result registration.BeaconInitialOpen pqxdh.BeaconAborted))
    (phase : registration.BeaconInitialOpen)
    (normal : ∃ result, call = ok result ∧ beaconMetadataOutcome expected result)
    (actual : call = ok (.Ok phase)) : BeaconPhaseMetadata expected phase := by
  obtain ⟨result, source, metadata⟩ := normal
  have resultEq : result = .Ok phase := by simpa using source.symm.trans actual
  simpa only [resultEq, beaconMetadataOutcome] using metadata

/-- Every finite live execution from the actual initial constructor keeps its exact source agreement and metadata. -/
theorem reachable_metadata (initial : registration.BeaconInitialKdf) (phase : registration.BeaconInitialOpen)
    (reachable : BeaconRecordReachable initial phase) : BeaconPhaseMetadata initial.agreement phase := by
  induction reachable with
  | transcript pending current put replacement prior actual ih =>
    obtain ⟨selected, back, getter, kept⟩ := beacon_transcript_metadata initial.agreement pending ih
    have pairEq : (selected, back) = (current, put) := by simpa using getter.symm.trans actual
    have putEq : back = put := congrArg Prod.snd pairEq
    simpa only [putEq] using kept replacement
  | start response phase actual =>
    cases response with
    | none =>
      simp [registration.BeaconInitialKdf.resume, pqxdh.beacon_abort_candidate] at actual
    | some response =>
      exact metadata_of_success initial.agreement (initial.resume (.Some response)) phase
        (beacon_initial_metadata initial response) actual
  | kdf pending response phase prior actual ih =>
    exact metadata_of_success initial.agreement (pending.resume response) phase
      (beacon_kdf_metadata initial.agreement pending response ih) actual
  | commitment pending matched phase prior actual ih =>
    exact metadata_of_success initial.agreement (pending.resume matched) phase
      (beacon_commitment_metadata initial.agreement pending matched ih) actual

/-- Exact completion over actual source-owned AD, metadata, plaintext and returned receive kernel. -/
def BeaconRecordCompletionSpec (pending : registration.BeaconRecordAead)
    (plaintext : core.option.Option (Slice Std.U8)) (kernel : ratchet.concrete.ConcreteRatchetKernel) : Prop :=
  pending.pending.pending.opening.context.associated_data = pending.agreement.binding.associated_data ∧
      pending.pending.finish plaintext = ok (kernel,
        match plaintext with
        | .None => .None
        | .Some bytes => .Some (⟨bytes, pending.agreement.candidate.server_binding.identity_key_id,
            1#u64⟩ : record.OpenedRecord (Slice Std.U8))) ∧
      pending.finish plaintext = ok (match plaintext with
        | .None => .Err ⟨pending.agreement.candidate.server_binding.identity_key_id⟩
        | .Some bytes =>
          if 8 < bytes.val.length ∧ (bytes.val.take 8).map absByte =
              Pqxdh.LE64 pending.agreement.candidate.assigned_key_id.val
            then .Ok (completedBeacon pending kernel bytes)
            else .Err ⟨pending.agreement.candidate.server_binding.identity_key_id⟩)

/-- Every finite actual live execution reaches exactly the pinned initial record gate, with no independent kernel, metadata or validity premise. -/
theorem reachable_completion (initial : registration.BeaconInitialKdf)
    (pending : registration.BeaconRecordAead) (plaintext : core.option.Option (Slice Std.U8))
    (reachable : BeaconRecordReachable initial (.AeadRequested pending)) :
    ∃ kernel, pending.agreement = initial.agreement ∧ BeaconRecordCompletionSpec pending plaintext kernel := by
  have metadata := reachable_metadata initial (.AeadRequested pending) reachable
  have own : BeaconPhaseMetadata pending.agreement (.AeadRequested pending) := by
    simpa only [← metadata.1] using metadata
  obtain ⟨kernel, completed⟩ := beacon_reachable_completion_refines pending plaintext own
  exact ⟨kernel, metadata.1, completed⟩

end BeaconcryptCore.Refinement.RegistrationReachability

/-- info: 'BeaconcryptCore.Refinement.RegistrationReachability.metadata_of_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationReachability.metadata_of_success

/-- info: 'BeaconcryptCore.Refinement.RegistrationReachability.reachable_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationReachability.reachable_metadata

/-- info: 'BeaconcryptCore.Refinement.RegistrationReachability.reachable_completion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationReachability.reachable_completion

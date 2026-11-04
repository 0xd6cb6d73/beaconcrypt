-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconCommitmentGenuine

/-! The actual Beacon hash phase retains the authenticated response's complete payload view and full source commitment fields, derived from its initializer and reached KDF callbacks. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconRecordFields
open BeaconcryptCore.Refinement.RegistrationRecords
open BeaconcryptCore.Refinement.NativeRecordWrapper
open BeaconcryptCore.Refinement.CommitmentSurface
open RegistrationNativeBeaconRecordTrace (Trace)

/-- Every successful initial continuation establishes the literal authenticated payload metadata. -/
theorem initial (pending : registration.BeaconInitialKdf)
    (reply : core.option.Option pqxdh.concrete.InitialRatchetKdfResponse) (next : registration.BeaconInitialOpen)
    (actual : pending.resume reply = .ok (.Ok next)) : BeaconPhaseMetadata pending.agreement next := by
  cases reply with
  | none => simp [registration.BeaconInitialKdf.resume, pqxdh.beacon_abort_candidate] at actual
  | some response =>
    obtain ⟨result, resumed, metadata⟩ := beacon_initial_metadata pending response
    have resultEq : result = .Ok next := RustM.ok.inj (resumed.symm.trans actual)
    cases resultEq
    exact metadata

/-- The reached KDF prefix preserves the exact agreement, ciphertext, full AD, sender and implicit sequence. -/
theorem along_prefix {S : Type} (implementation : QueryImpl RegistrationRecordPrimitives.Spec (StateT S ProbComp))
    (expected : agreement.BeaconAgreement) {first last : registration.BeaconInitialOpen} {before after : S}
    (actual : RegistrationNativeBeaconRecordTrace.Prefix implementation first before last after)
    (prior : BeaconPhaseMetadata expected first) : BeaconPhaseMetadata expected last := by
  induction actual with
  | refl => exact prior
  | step pending request reply next before middle after last requested called resumed following ih =>
    obtain ⟨result, executed, metadata⟩ := beacon_kdf_metadata expected pending reply prior
    have resultEq : result = .Ok next := RustM.ok.inj (executed.symm.trans resumed)
    cases resultEq
    exact ih metadata

/-- The actual hash transcript is the production CTX357 of the selected source material and the authenticated full payload context. -/
theorem transcript {S : Type} (implementation : QueryImpl RegistrationRecordPrimitives.Spec (StateT S ProbComp))
    (expected : agreement.BeaconAgreement) (phase : registration.BeaconInitialOpen)
    (completed : registration.CompletedBeacon) (before after : S)
    (trace : Trace implementation phase completed before after)
    (metadata : BeaconPhaseMetadata expected phase)
    (genuine : RegistrationNativeBeaconCommitmentGenuine.Genuine phase) :
    ∃ fields : Fields, trace.transcript.bytes = productionInput fields ∧
      fields.associatedData = expected.binding.associated_data ∧ fields.sequence = 1#u64 ∧
      fields.senderId = expected.candidate.server_binding.identity_key_id ∧
      fields.tag.val = (expected.application_ciphertext.val.take (expected.application_ciphertext.val.length - 64)).drop
        (expected.application_ciphertext.val.length - 80) ∧
      trace.supplied.val = expected.application_ciphertext.val.drop (expected.application_ciphertext.val.length - 64) := by
  have kept := along_prefix implementation expected trace.leading metadata
  obtain ⟨material, sequence, selected, sequenced, built⟩ :=
    RegistrationNativeBeaconCommitmentGenuine.along_prefix implementation trace.leading genuine
  have sequenceEq : sequence = 1#u64 := RustM.ok.inj (sequenced.symm.trans kept.2.1)
  have view := kept.2.2
  have requested := trace.hashRequested
  change (.ok trace.commitmentState.pending.pending.transcript : RustM commitment.CommitmentTranscript) = .ok trace.transcript at requested
  have transcriptEq := congrArg commitment.CommitmentTranscript.bytes (RustM.ok.inj requested)
  have supplied := trace.suppliedRequested
  change (.ok trace.commitmentState.pending.pending.opening.context.commitment : RustM (Std.Array U8 64#usize)) = .ok trace.supplied at supplied
  refine ⟨selectedFields trace.commitmentState.pending.pending.opening material sequence, transcriptEq.symm.trans built,
    view.2.2.2.1, sequenceEq, view.2.2.2.2, view.2.1, ?_⟩
  rw [← RustM.ok.inj supplied]
  exact view.2.2.1

end BeaconcryptCore.Computational.RegistrationNativeBeaconRecordFields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconRecordFields.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconRecordFields.initial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconRecordFields.along_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconRecordFields.along_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconRecordFields.transcript' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconRecordFields.transcript

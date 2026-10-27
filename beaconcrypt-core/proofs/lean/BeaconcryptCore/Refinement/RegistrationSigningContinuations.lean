-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.Authentication
import BeaconcryptCore.PanicFreedom.SessionBinding
import BeaconcryptCore.PanicFreedom.Pqxdh
import BeaconcryptCore.PanicFreedom.RegistrationTrivial
import BeaconcryptCore.Refinement.RegistrationInputs

/-! Exact outgoing registration continuations over arbitrary represented states and primitive replies. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Refinement.RegistrationSigningContinuations

theorem begin_beacon_init_exact (control : pqxdh.BeaconFresh)
    (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Array Std.U8 1952#usize) :
    ∃ started, pqxdh.beacon_start control inputs coins = ok started ∧
      registration.begin_beacon_init control inputs coins pin mldsa =
        if control.expected_server_binding.identity_key_id ≠ pin.binding.identity_key_id ∨
            absBytes control.expected_server_binding.identity_public_key ≠ absBytes pin.binding.identity_public_key
        then ok (.Rejected control)
        else ok (.Ed25519SigningRequested {
          state := {
            original_control := control
            started := started
            server_pin := pin
            beacon_identity := inputs.identity_public_key
            beacon_mldsa := mldsa
            pre_key := Array.repeat 98#usize 0#u8
            one_time_key := Array.repeat 98#usize 0#u8
            pq_key := Array.repeat 1249#usize 0#u8 }
          stage := .PreKey }) := by
  obtain ⟨started, startedRun⟩ := BeaconcryptCore.PanicFreedom.beacon_start_ok control inputs coins
  refine ⟨started, startedRun, ?_⟩
  simp [registration.begin_beacon_init, pqxdh.BeaconFresh.impl.expected_server_binding,
    session.ServerAuthenticationPin.impl.binding, core.Array.Insts.CoreCmpPartialEqArray.ne,
    array_eq_abs, startedRun]
  split_ifs
  all_goals simp_all

/-- All attached Ed fields are retained in the exact unsigned Init view. -/
def retainedFields (state : registration.BeaconInitState) : authentication.InitFields := {
  identity_key := state.started.message.identity_key
  pre_key := state.pre_key
  one_time_key := state.one_time_key
  pq_key := state.pq_key
  mldsa_public_key := state.beacon_mldsa }

theorem retained_fields_exact (state : registration.BeaconInitState) :
    registration.BeaconInitState.fields state = ok (retainedFields state) := by
  rfl

/-- Fingerprinting retains the complete attached fields and both selected server pins in the actual hash request. -/
theorem beacon_fingerprint_some_exact (self : registration.BeaconFingerprint)
    (fingerprint : Array Std.U8 64#usize) :
    ∃ next, registration.BeaconFingerprint.resume self (.Some fingerprint) =
        ok (.HashRequested next) ∧
      next.state = self.state ∧ next.fingerprint = fingerprint ∧
      ∃ request, registration.BeaconInitHash.request next = ok request ∧
        RegistrationInputs.hashBytes request =
          Pqxdh.TranscriptAuth.initTranscript
            (TranscriptAuthRefinement.absInit (retainedFields self.state))
            (TranscriptAuthRefinement.absId self.state.server_pin.binding.identity_key_id)
            (absBytes self.state.server_pin.binding.identity_public_key)
            (absBytes self.state.server_pin.public_key) := by
  obtain ⟨input, inputRun, inputBytes⟩ := TranscriptAuthRefinement.build_init_transcript_abs
    (retainedFields self.state) self.state.server_pin.binding.identity_key_id
    self.state.server_pin.binding.identity_public_key self.state.server_pin.public_key
  refine ⟨{ state := self.state, fingerprint, input }, ?_, rfl, rfl, ?_⟩
  · simp only [registration.BeaconFingerprint.resume, session.ServerAuthenticationPin.impl.binding,
      session.ServerAuthenticationPin.impl.public_key, retained_fields_exact, inputRun, bind_tc_ok]
  · refine ⟨_, rfl, ?_⟩
    exact inputBytes

/-- The exact returned digest determines the retained ML key, role, context and signature input. -/
theorem beacon_init_hash_some_exact (self : registration.BeaconInitHash)
    (digest : Array Std.U8 64#usize) :
    ∃ next, registration.BeaconInitHash.resume self (.Some digest) =
        ok (.MldsaSigningRequested next) ∧
      next.state = self.state ∧ next.fingerprint = self.fingerprint ∧ next.init_hash = digest ∧
      ∃ request, registration.BeaconMldsaSigning.request next = ok request ∧
        request.public_key = self.state.beacon_mldsa ∧ request.role = .Beacon ∧
        request.context = authentication.SIGNING_CONTEXT ∧
        absBytes request.context = Pqxdh.TranscriptAuth.signingContext ∧
        absBytes request.input = Pqxdh.TranscriptAuth.signatureInput .beacon (absBytes digest) := by
  obtain ⟨input, inputRun, inputBytes⟩ :=
    TranscriptAuthInputsRefinement.build_signature_input_abs .Beacon digest
  refine ⟨{ state := self.state, fingerprint := self.fingerprint, init_hash := digest, input },
    ?_, rfl, rfl, rfl, _, rfl, rfl, rfl, rfl,
    TranscriptAuthInputsRefinement.signing_context_abs, inputBytes⟩
  simp only [registration.BeaconInitHash.resume, inputRun, bind_tc_ok]

/-- A supplied signature is admitted exactly at its fixed width; successful message and binding views keep the same retained inputs. -/
def signatureResult (self : registration.BeaconMldsaSigning) (signature : Slice Std.U8) :
    registration.BeaconInitEffect → Prop
  | .Rejected original => original = self.state.original_control ∧ signature.val.length ≠ 3309
  | .Ready ready => signature.val.length = 3309 ∧ ready.state = self.state ∧
      ready.signature.val = signature.val ∧ ready.binding.server_pin = self.state.server_pin ∧
      ready.binding.init_hash = self.init_hash ∧
      ready.binding.beacon_identity_public_key = self.state.beacon_identity ∧
      ready.binding.beacon_fingerprint = self.fingerprint ∧
      ∃ message, registration.BeaconInitReady.message ready = ok message ∧
        message.fields = retainedFields self.state ∧ message.signature.val = signature.val
  | _ => False

theorem beacon_mldsa_signature_exact (self : registration.BeaconMldsaSigning)
    (signature : Slice Std.U8) :
    ∃ result, registration.BeaconMldsaSigning.resume self (.Some signature) = ok result ∧
      signatureResult self signature result := by
  obtain ⟨copied, copiedRun, copiedFacts⟩ := RegistrationInputs.copied_slice_exact 3309#usize signature
  cases copied with
  | Ok copied =>
    obtain ⟨binding, bindingRun, bindingFacts⟩ := SessionBinding.registration_new_refines
      self.state.server_pin self.init_hash self.state.beacon_identity self.fingerprint
    refine ⟨.Ready { state := self.state, binding, signature := copied }, ?_,
      copiedFacts.2, rfl, copiedFacts.1, bindingFacts.1, bindingFacts.2.1,
      bindingFacts.2.2.1, bindingFacts.2.2.2.1, _, rfl, rfl, copiedFacts.1⟩
    simp only [registration.BeaconMldsaSigning.resume, copiedRun, bindingRun, bind_tc_ok]
  | Err error =>
    refine ⟨.Rejected self.state.original_control, ?_, rfl, copiedFacts⟩
    simp only [registration.BeaconMldsaSigning.resume, copiedRun, bind_tc_ok]

/-- Every missing primitive reply rejects with the same original Fresh state. -/
theorem missing_reply_rejects_exact (fingerprint : registration.BeaconFingerprint)
    (hash : registration.BeaconInitHash) (signing : registration.BeaconMldsaSigning) :
    registration.BeaconFingerprint.resume fingerprint .None = ok (.Rejected fingerprint.state.original_control) ∧
      registration.BeaconInitHash.resume hash .None = ok (.Rejected hash.state.original_control) ∧
      registration.BeaconMldsaSigning.resume signing .None = ok (.Rejected signing.state.original_control) := by
  exact ⟨rfl, rfl, rfl⟩

end BeaconcryptCore.Refinement.RegistrationSigningContinuations

/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningContinuations.begin_beacon_init_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningContinuations.begin_beacon_init_exact

/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningContinuations.retained_fields_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningContinuations.retained_fields_exact

/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningContinuations.beacon_fingerprint_some_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningContinuations.beacon_fingerprint_some_exact

/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningContinuations.beacon_init_hash_some_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningContinuations.beacon_init_hash_some_exact

/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningContinuations.beacon_mldsa_signature_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningContinuations.beacon_mldsa_signature_exact

/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningContinuations.missing_reply_rejects_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningContinuations.missing_reply_rejects_exact

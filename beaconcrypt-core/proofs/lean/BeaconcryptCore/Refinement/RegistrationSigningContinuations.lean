-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.Authentication
import BeaconcryptCore.PanicFreedom.Pqxdh
import BeaconcryptCore.Refinement.RegistrationInputs
import BeaconcryptCore.Refinement.SessionBinding

/-! Exact outgoing registration continuations over arbitrary represented states and primitive replies. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Refinement.RegistrationSigningContinuations

theorem begin_beacon_init_exact (control : pqxdh.BeaconFresh)
    (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) :
    ∃ started, pqxdh.beacon_start control inputs coins = ok started ∧
      registration.begin_beacon_init control inputs coins pin =
        if control.expected_server_binding.identity_key_id ≠ pin.binding.identity_key_id ∨
            absBytes control.expected_server_binding.identity_public_key ≠ absBytes pin.binding.identity_public_key
        then ok (.Rejected control)
        else ok (.Ed25519SigningRequested {
          state := {
            original_control := control
            started := started
            server_pin := pin
            beacon_identity := inputs.identity_public_key
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

/-- All attached Ed fields are retained in the exact remaining Init view. -/
def retainedFields (state : registration.BeaconInitState) : authentication.InitFields := {
  identity_key := state.started.message.identity_key
  pre_key := state.pre_key
  one_time_key := state.one_time_key
  pq_key := state.pq_key }

theorem retained_fields_exact (state : registration.BeaconInitState) :
    registration.BeaconInitState.fields state = ok (retainedFields state) := by
  rfl

/-- The request-hash effect borrows only the exact core-selected request preimage. -/
theorem beacon_init_hash_request_exact (self : registration.BeaconInitHash) :
    ∃ request, self.request = ok request ∧ RegistrationInputs.hashBytes request = absBytes self.input :=
  ⟨_, rfl, rfl⟩

/-- A supplied digest is retained for pinned-Server response authentication; no Beacon ML signing follows. -/
theorem beacon_init_hash_some_exact (self : registration.BeaconInitHash)
    (digest : Array Std.U8 64#usize) :
    ∃ ready, self.resume (.Some digest) = ok (.Ready ready) ∧
      ready.state = self.state ∧ ready.init_hash = digest ∧
      ∃ message, ready.message = ok message ∧ message.fields = retainedFields self.state := by
  exact ⟨_, rfl, rfl, rfl, _, rfl, rfl⟩

/-- A missing request hash preserves the original Fresh control. -/
theorem missing_reply_rejects_exact (hash : registration.BeaconInitHash) :
    hash.resume .None = ok (.Rejected hash.state.original_control) := rfl

/-- Failed serialization creates no published pending capability. -/
theorem failed_publication_preserves_fresh (self : registration.BeaconInitReady) (Encoded : Type) :
    self.publish (Encoded := Encoded) .None = ok (.Err self.state.original_control) := rfl

/-- Only successful publication owns the exact request buffers and digest in the pending binding. -/
theorem publication_retains_exact_request (self : registration.BeaconInitReady)
    {Encoded : Type} (encoded : Encoded) :
    ∃ published, self.publish (.Some encoded) = ok (.Ok published) ∧
      published.pending.control = self.state.started.state ∧
      published.pending.binding.server_pin = self.state.server_pin ∧
      published.pending.binding.init_hash = self.init_hash ∧
      published.pending.binding.init_fields.identity_key = self.state.started.message.identity_key ∧
      published.pending.binding.init_fields.pre_key = self.state.pre_key ∧
      published.pending.binding.init_fields.one_time_key = self.state.one_time_key ∧
      published.pending.binding.init_fields.pq_key = self.state.pq_key ∧ published.encoded = encoded := by
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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

/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningContinuations.beacon_init_hash_request_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningContinuations.beacon_init_hash_request_exact

/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningContinuations.beacon_init_hash_some_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningContinuations.beacon_init_hash_some_exact

/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningContinuations.missing_reply_rejects_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningContinuations.missing_reply_rejects_exact

/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningContinuations.failed_publication_preserves_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningContinuations.failed_publication_preserves_fresh

/-- info: 'BeaconcryptCore.Refinement.RegistrationSigningContinuations.publication_retains_exact_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationSigningContinuations.publication_retains_exact_request

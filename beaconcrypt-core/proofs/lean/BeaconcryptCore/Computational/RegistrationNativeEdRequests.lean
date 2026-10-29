-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEdOrigin
import BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter
import BeaconcryptCore.Refinement.RegistrationSigningContinuations
import BeaconcryptCore.Refinement.RegistrationSigning

/-! The actual outgoing controller requests only the tagged source prekey/PQ/one-time messages. Its resumed signing stages retain the complete unsigned builder state, so retries and partial failures do not require a synthetic successful-publication ledger. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeEdRequests
open PqxdhEd25519EufCma
open RegistrationNativeEdOrigin (Allowed)
open BeaconcryptCore.Refinement.RegistrationSigning

def Shape (prekey : X25519PublicKey) (started : pqxdh.BeaconStart) : Prop :=
  absBytes started.message.prekey = prekeyMessage prekey ∧
    (∃ key : X25519PublicKey, absBytes started.message.one_time_key = oneTimeMessage key) ∧
    (∃ key : PqxdhKemIndCca.MlKem768PublicKey, absBytes started.message.pq_key = pqMessage key)

/-- Every actual request belongs to the source's tagged message family, including requests followed by a rejected signature or publication. -/
theorem request_allowed (prekey : X25519PublicKey) (pending : registration.BeaconEd25519Signing)
    (shape : Shape prekey pending.state.started) (request : registration.Ed25519SigningRequest)
    (requested : pending.request = .ok request) : Allowed prekey (TranscriptAuthParts.absSlice request.message) := by
  obtain ⟨actual, exactRequest, _key, _role, message⟩ := ed_request_exact pending
  have equal : actual = request := RustM.ok.inj (exactRequest.symm.trans requested)
  subst request
  simp only [TranscriptAuthParts.absSlice, message]
  cases stage : pending.stage
  all_goals simp only [signingMessageValues, stage]
  · change Allowed prekey (absBytes pending.state.started.message.prekey)
    rw [shape.1]
    exact Or.inl rfl
  · change Allowed prekey (absBytes pending.state.started.message.one_time_key)
    exact Or.inr (Or.inr shape.2.1)
  · change Allowed prekey (absBytes pending.state.started.message.pq_key)
    exact Or.inr (Or.inl shape.2.2)

/-- Advancing an attached-signature continuation retains the entire original unsigned builder state. -/
theorem resume_started (pending next : registration.BeaconEd25519Signing)
    (reply : core.option.Option (Slice U8))
    (resumed : pending.resume reply = .ok (.Ed25519SigningRequested next)) :
    next.state.started = pending.state.started := by
  obtain ⟨effect, actual, progress⟩ := ed_resume_refines pending reply
  have equal : effect = .Ed25519SigningRequested next := RustM.ok.inj (actual.symm.trans resumed)
  subst effect
  cases stage : pending.stage
  all_goals simp only [EdReplyTransition, stage] at progress
  · simpa only using congrArg (fun state : registration.BeaconInitState => state.started) progress.2.2.2
  · simpa only using congrArg (fun state : registration.BeaconInitState => state.started) progress.2.2.2
  · exact progress.2.elim

/-- The real native entry point derives the signing shape from its actual unsigned builder, retaining its pin-rejection branch. -/
theorem begin_shape (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize)
    (prekey oneTime : X25519PublicKey) (pq : PqxdhKemIndCca.MlKem768PublicKey)
    (prekeyBytes : absBytes inputs.prekey_public_key = prekey.toList)
    (oneTimeBytes : absBytes coins.one_time_public_key = oneTime.toList)
    (pqBytes : absBytes inputs.pq_public_key = pq.toList)
    (pending : registration.BeaconEd25519Signing)
    (begun : registration.begin_beacon_init control inputs coins pin mldsa = .ok (.Ed25519SigningRequested pending)) :
    Shape prekey pending.state.started := by
  obtain ⟨started, built, _pin, _identity, pre, one, kem⟩ :=
    PqxdhJointPhase1SourceWriter.beacon_start_unsigned control inputs coins
  obtain ⟨actual, actualBuild, exactBegin⟩ :=
    BeaconcryptCore.Refinement.RegistrationSigningContinuations.begin_beacon_init_exact control inputs coins pin mldsa
  have same : started = actual := RustM.ok.inj (built.symm.trans actualBuild)
  subst actual
  rw [exactBegin] at begun
  split at begun
  · cases begun
  · have equal := registration.BeaconInitEffect.Ed25519SigningRequested.inj (RustM.ok.inj begun)
    subst pending
    refine ⟨?_, ⟨oneTime, ?_⟩, ⟨pq, ?_⟩⟩
    · simpa only [prekeyBytes, prekeyMessage] using pre
    · simpa only [oneTimeBytes, oneTimeMessage] using one
    · simpa only [pqBytes, pqMessage] using kem

end BeaconcryptCore.Computational.RegistrationNativeEdRequests

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdRequests.request_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdRequests.request_allowed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdRequests.resume_started' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdRequests.resume_started
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEdRequests.begin_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEdRequests.begin_shape

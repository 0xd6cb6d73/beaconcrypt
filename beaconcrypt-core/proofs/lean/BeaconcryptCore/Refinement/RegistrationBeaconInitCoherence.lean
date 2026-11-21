-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationSigningContinuations
import BeaconcryptCore.Refinement.RegistrationSigning
import BeaconcryptCore.Refinement.PqxdhSurface

/-! The actual outgoing Init gate checks the classical pin before any signature or hash callback. Every subsequent native continuation retains that checked binding, so a published Beacon pending control and its authenticated registration binding agree by source execution. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Refinement.RegistrationBeaconInitCoherence

def StateCoherent (state : registration.BeaconInitState) : Prop :=
  state.started.state.expected_server_binding = state.server_pin.binding

def Coherent : registration.BeaconInitEffect → Prop
  | .Rejected _ => True
  | .Ed25519SigningRequested pending => StateCoherent pending.state
  | .HashRequested pending => StateCoherent pending.state
  | .Ready pending => StateCoherent pending.state

private theorem binding_eq (left right : pqxdh.ServerBinding)
    (keyId : left.identity_key_id = right.identity_key_id)
    (key : absBytes left.identity_public_key = absBytes right.identity_public_key) : left = right := by
  have keyEq := PqxdhSurface.bytes_eq_of_abs_eq key
  cases left
  cases right
  cases keyEq
  cases keyId
  rfl

theorem begin_coherent (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs)
    (coins : pqxdh.BeaconCoins) (pin : session.ServerAuthenticationPin)
    (effect : registration.BeaconInitEffect)
    (actual : registration.begin_beacon_init control inputs coins pin = .ok effect) : Coherent effect := by
  obtain ⟨started, startedRun, _validation, retained, _identity⟩ := PqxdhSurface.beacon_start_validates control inputs coins
  obtain ⟨other, otherRun, beginRun⟩ := RegistrationSigningContinuations.begin_beacon_init_exact control inputs coins pin
  have same : started = other := RustM.ok.inj (startedRun.symm.trans otherRun)
  subst other
  rw [beginRun] at actual
  split_ifs at actual with mismatch
  · cases actual
    trivial
  · cases actual
    exact retained.trans (binding_eq _ _ (not_ne_iff.mp (not_or.mp mismatch).1)
      (not_ne_iff.mp (not_or.mp mismatch).2))

theorem ed_coherent (before : registration.BeaconEd25519Signing)
    (reply : core.option.Option (Slice Std.U8)) (effect : registration.BeaconInitEffect)
    (coherent : StateCoherent before.state) (actual : before.resume reply = .ok effect) : Coherent effect := by
  obtain ⟨result, resumed, progress⟩ := RegistrationSigning.ed_resume_refines before reply
  have same : result = effect := RustM.ok.inj (resumed.symm.trans actual)
  subst effect
  cases result with
  | Rejected original => trivial
  | Ed25519SigningRequested after =>
      cases stage : before.stage
      all_goals simp only [RegistrationSigning.EdReplyTransition, stage] at progress
      · exact (congrArg StateCoherent progress.2.2.2).mpr coherent
      · exact (congrArg StateCoherent progress.2.2.2).mpr coherent
      · exact progress.2.elim
  | HashRequested after =>
      exact (congrArg StateCoherent progress.2.2.2).mpr coherent
  | Ready ready => exact progress.elim

theorem hash_coherent (before : registration.BeaconInitHash)
    (reply : core.option.Option (Std.Array Std.U8 64#usize)) (effect : registration.BeaconInitEffect)
    (coherent : StateCoherent before.state) (actual : before.resume reply = .ok effect) : Coherent effect := by
  cases reply with
  | none => cases actual; trivial
  | some digest =>
      cases actual
      exact coherent

theorem publish_coherent {Encoded : Type} (ready : registration.BeaconInitReady)
    (encoded : core.option.Option Encoded) (published : registration.PublishedBeaconInit Encoded)
    (coherent : Coherent (.Ready ready)) (actual : ready.publish encoded = .ok (.Ok published)) :
    published.pending.control.expected_server_binding = published.pending.binding.server_pin.binding := by
  cases encoded with
  | none => simp [registration.BeaconInitReady.publish] at actual
  | some bytes =>
      obtain ⟨result, ran, controlSame, pinSame, _⟩ :=
        RegistrationSigningContinuations.publication_retains_exact_request ready bytes
      have same : result = published := core.result.Result.Ok.inj (RustM.ok.inj (ran.symm.trans actual))
      subst result
      rw [controlSame, pinSame]
      exact coherent

end BeaconcryptCore.Refinement.RegistrationBeaconInitCoherence

/-- info: 'BeaconcryptCore.Refinement.RegistrationBeaconInitCoherence.begin_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationBeaconInitCoherence.begin_coherent
/-- info: 'BeaconcryptCore.Refinement.RegistrationBeaconInitCoherence.ed_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationBeaconInitCoherence.ed_coherent
/-- info: 'BeaconcryptCore.Refinement.RegistrationBeaconInitCoherence.hash_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationBeaconInitCoherence.hash_coherent
/-- info: 'BeaconcryptCore.Refinement.RegistrationBeaconInitCoherence.publish_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationBeaconInitCoherence.publish_coherent

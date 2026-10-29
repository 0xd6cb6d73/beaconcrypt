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
  | .FingerprintRequested pending => StateCoherent pending.state
  | .HashRequested pending => StateCoherent pending.state
  | .MldsaSigningRequested pending => StateCoherent pending.state
  | .Ready pending => pending.state.started.state.expected_server_binding = pending.binding.server_pin.binding

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
    (coins : pqxdh.BeaconCoins) (pin : session.ServerAuthenticationPin) (mldsa : Std.Array Std.U8 1952#usize)
    (effect : registration.BeaconInitEffect)
    (actual : registration.begin_beacon_init control inputs coins pin mldsa = .ok effect) : Coherent effect := by
  obtain ⟨started, startedRun, _validation, retained, _identity⟩ := PqxdhSurface.beacon_start_validates control inputs coins
  obtain ⟨other, otherRun, beginRun⟩ := RegistrationSigningContinuations.begin_beacon_init_exact control inputs coins pin mldsa
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
  | FingerprintRequested after =>
      exact (congrArg StateCoherent progress.2.2.2).mpr coherent
  | HashRequested after => exact progress.elim
  | MldsaSigningRequested after => exact progress.elim
  | Ready ready => exact progress.elim

theorem fingerprint_coherent (before : registration.BeaconFingerprint)
    (reply : core.option.Option (Std.Array Std.U8 64#usize)) (effect : registration.BeaconInitEffect)
    (coherent : StateCoherent before.state) (actual : before.resume reply = .ok effect) : Coherent effect := by
  cases reply with
  | none => cases actual; trivial
  | some digest =>
      obtain ⟨next, resumed, stateSame, _fingerprint, _request⟩ :=
        RegistrationSigningContinuations.beacon_fingerprint_some_exact before digest
      rw [resumed] at actual
      cases actual
      change StateCoherent next.state
      rw [stateSame]
      exact coherent

theorem hash_coherent (before : registration.BeaconInitHash)
    (reply : core.option.Option (Std.Array Std.U8 64#usize)) (effect : registration.BeaconInitEffect)
    (coherent : StateCoherent before.state) (actual : before.resume reply = .ok effect) : Coherent effect := by
  cases reply with
  | none => cases actual; trivial
  | some digest =>
      obtain ⟨next, resumed, stateSame, _fingerprint, _digest, _request⟩ :=
        RegistrationSigningContinuations.beacon_init_hash_some_exact before digest
      rw [resumed] at actual
      cases actual
      change StateCoherent next.state
      rw [stateSame]
      exact coherent

theorem mldsa_coherent (before : registration.BeaconMldsaSigning)
    (reply : core.option.Option (Slice Std.U8)) (effect : registration.BeaconInitEffect)
    (coherent : StateCoherent before.state) (actual : before.resume reply = .ok effect) : Coherent effect := by
  cases reply with
  | none => cases actual; trivial
  | some signature =>
      obtain ⟨result, resumed, progress⟩ := RegistrationSigningContinuations.beacon_mldsa_signature_exact before signature
      have same : result = effect := RustM.ok.inj (resumed.symm.trans actual)
      subst effect
      cases result with
      | Rejected original => trivial
      | Ready ready =>
          change ready.state.started.state.expected_server_binding = ready.binding.server_pin.binding
          rw [progress.2.2.2.1, progress.2.1]
          exact coherent
      | Ed25519SigningRequested after => exact progress.elim
      | FingerprintRequested after => exact progress.elim
      | HashRequested after => exact progress.elim
      | MldsaSigningRequested after => exact progress.elim

theorem publish_coherent {Encoded : Type} (ready : registration.BeaconInitReady)
    (encoded : core.option.Option Encoded) (published : registration.PublishedBeaconInit Encoded)
    (coherent : Coherent (.Ready ready)) (actual : ready.publish encoded = .ok (.Ok published)) :
    published.pending.control.expected_server_binding = published.pending.binding.server_pin.binding := by
  cases encoded with
  | none => simp [registration.BeaconInitReady.publish] at actual
  | some bytes =>
      simp only [registration.BeaconInitReady.publish, RustM.ok.injEq, core.result.Result.Ok.injEq] at actual
      cases actual
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
/-- info: 'BeaconcryptCore.Refinement.RegistrationBeaconInitCoherence.fingerprint_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationBeaconInitCoherence.fingerprint_coherent
/-- info: 'BeaconcryptCore.Refinement.RegistrationBeaconInitCoherence.hash_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationBeaconInitCoherence.hash_coherent
/-- info: 'BeaconcryptCore.Refinement.RegistrationBeaconInitCoherence.mldsa_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationBeaconInitCoherence.mldsa_coherent
/-- info: 'BeaconcryptCore.Refinement.RegistrationBeaconInitCoherence.publish_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationBeaconInitCoherence.publish_coherent

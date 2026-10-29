-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationSigningContinuations
import BeaconcryptCore.Refinement.RegistrationSigning
import BeaconcryptCore.Refinement.PqxdhSurface

/-! The actual outgoing Init gate checks the classical pin before any signature or hash callback. Every subsequent native continuation retains that checked binding, so a published Beacon pending control and its authenticated registration binding agree by source execution. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement BeaconcryptCore.Refinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationBeaconInitPin

def StateCoherent (expected : pqxdh.ServerBinding) (state : registration.BeaconInitState) : Prop :=
  state.started.state.expected_server_binding = expected

def Coherent (expected : pqxdh.ServerBinding) : registration.BeaconInitEffect → Prop
  | .Rejected _ => True
  | .Ed25519SigningRequested pending => StateCoherent expected pending.state
  | .FingerprintRequested pending => StateCoherent expected pending.state
  | .HashRequested pending => StateCoherent expected pending.state
  | .MldsaSigningRequested pending => StateCoherent expected pending.state
  | .Ready pending => StateCoherent expected pending.state

variable {expected : pqxdh.ServerBinding}

theorem begin_coherent (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs)
    (coins : pqxdh.BeaconCoins) (pin : session.ServerAuthenticationPin) (mldsa : Std.Array Std.U8 1952#usize)
    (effect : registration.BeaconInitEffect)
    (actual : registration.begin_beacon_init control inputs coins pin mldsa = .ok effect) : Coherent control.expected_server_binding effect := by
  obtain ⟨started, startedRun, _validation, retained, _identity⟩ := PqxdhSurface.beacon_start_validates control inputs coins
  obtain ⟨other, otherRun, beginRun⟩ := RegistrationSigningContinuations.begin_beacon_init_exact control inputs coins pin mldsa
  have same : started = other := RustM.ok.inj (startedRun.symm.trans otherRun)
  subst other
  rw [beginRun] at actual
  split_ifs at actual with mismatch
  · cases actual
    trivial
  · cases actual
    exact retained

theorem ed_coherent (before : registration.BeaconEd25519Signing)
    (reply : core.option.Option (Slice Std.U8)) (effect : registration.BeaconInitEffect)
    (coherent : StateCoherent expected before.state) (actual : before.resume reply = .ok effect) : Coherent expected effect := by
  obtain ⟨result, resumed, progress⟩ := RegistrationSigning.ed_resume_refines before reply
  have same : result = effect := RustM.ok.inj (resumed.symm.trans actual)
  subst effect
  cases result with
  | Rejected original => trivial
  | Ed25519SigningRequested after =>
      cases stage : before.stage
      all_goals simp only [RegistrationSigning.EdReplyTransition, stage] at progress
      · exact (congrArg (StateCoherent expected) progress.2.2.2).mpr coherent
      · exact (congrArg (StateCoherent expected) progress.2.2.2).mpr coherent
      · exact progress.2.elim
  | FingerprintRequested after =>
      exact (congrArg (StateCoherent expected) progress.2.2.2).mpr coherent
  | HashRequested after => exact progress.elim
  | MldsaSigningRequested after => exact progress.elim
  | Ready ready => exact progress.elim

theorem fingerprint_coherent (before : registration.BeaconFingerprint)
    (reply : core.option.Option (Std.Array Std.U8 64#usize)) (effect : registration.BeaconInitEffect)
    (coherent : StateCoherent expected before.state) (actual : before.resume reply = .ok effect) : Coherent expected effect := by
  cases reply with
  | none => cases actual; trivial
  | some digest =>
      obtain ⟨next, resumed, stateSame, _fingerprint, _request⟩ :=
        RegistrationSigningContinuations.beacon_fingerprint_some_exact before digest
      rw [resumed] at actual
      cases actual
      change StateCoherent expected next.state
      rw [stateSame]
      exact coherent

theorem hash_coherent (before : registration.BeaconInitHash)
    (reply : core.option.Option (Std.Array Std.U8 64#usize)) (effect : registration.BeaconInitEffect)
    (coherent : StateCoherent expected before.state) (actual : before.resume reply = .ok effect) : Coherent expected effect := by
  cases reply with
  | none => cases actual; trivial
  | some digest =>
      obtain ⟨next, resumed, stateSame, _fingerprint, _digest, _request⟩ :=
        RegistrationSigningContinuations.beacon_init_hash_some_exact before digest
      rw [resumed] at actual
      cases actual
      change StateCoherent expected next.state
      rw [stateSame]
      exact coherent

theorem mldsa_coherent (before : registration.BeaconMldsaSigning)
    (reply : core.option.Option (Slice Std.U8)) (effect : registration.BeaconInitEffect)
    (coherent : StateCoherent expected before.state) (actual : before.resume reply = .ok effect) : Coherent expected effect := by
  cases reply with
  | none => cases actual; trivial
  | some signature =>
      obtain ⟨result, resumed, progress⟩ := RegistrationSigningContinuations.beacon_mldsa_signature_exact before signature
      have same : result = effect := RustM.ok.inj (resumed.symm.trans actual)
      subst effect
      cases result with
      | Rejected original => trivial
      | Ready ready =>
          change ready.state.started.state.expected_server_binding = expected
          rw [progress.2.1]
          exact coherent
      | Ed25519SigningRequested after => exact progress.elim
      | FingerprintRequested after => exact progress.elim
      | HashRequested after => exact progress.elim
      | MldsaSigningRequested after => exact progress.elim

theorem publish_coherent {Encoded : Type} (ready : registration.BeaconInitReady)
    (encoded : core.option.Option Encoded) (published : registration.PublishedBeaconInit Encoded)
    (coherent : Coherent expected (.Ready ready)) (actual : ready.publish encoded = .ok (.Ok published)) :
    published.pending.control.expected_server_binding = expected := by
  cases encoded with
  | none => simp [registration.BeaconInitReady.publish] at actual
  | some bytes =>
      simp only [registration.BeaconInitReady.publish, RustM.ok.injEq, core.result.Result.Ok.injEq] at actual
      cases actual
      exact coherent

end BeaconcryptCore.Computational.RegistrationBeaconInitPin


/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitPin.begin_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitPin.begin_coherent

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitPin.ed_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitPin.ed_coherent

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitPin.fingerprint_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitPin.fingerprint_coherent

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitPin.hash_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitPin.hash_coherent

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitPin.mldsa_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitPin.mldsa_coherent

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitPin.publish_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitPin.publish_coherent

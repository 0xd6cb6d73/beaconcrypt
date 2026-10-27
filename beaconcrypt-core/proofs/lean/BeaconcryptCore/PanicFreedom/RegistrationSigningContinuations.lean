-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationSigningContinuations

/-! The four outgoing registration continuations return normally on arbitrary represented states and primitive replies. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core

set_option autoImplicit false

namespace BeaconcryptCore.PanicFreedom.RegistrationSigningContinuations

open BeaconcryptCore.Refinement.RegistrationSigningContinuations

theorem begin_beacon_init_total (control : pqxdh.BeaconFresh)
    (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Array Std.U8 1952#usize) :
    ∃ result, registration.begin_beacon_init control inputs coins pin mldsa = ok result := by
  obtain ⟨_, _, run⟩ := begin_beacon_init_exact control inputs coins pin mldsa
  split_ifs at run
  all_goals exact ⟨_, run⟩

theorem BeaconFingerprint_resume_total (self : registration.BeaconFingerprint)
    (fingerprint : core.option.Option (Array Std.U8 64#usize)) :
    ∃ result, registration.BeaconFingerprint.resume self fingerprint = ok result := by
  exact match fingerprint with
    | .None => ⟨_, rfl⟩
    | .Some value => (beacon_fingerprint_some_exact self value).elim fun next facts => ⟨_, facts.1⟩

theorem BeaconInitHash_resume_total (self : registration.BeaconInitHash)
    (digest : core.option.Option (Array Std.U8 64#usize)) :
    ∃ result, registration.BeaconInitHash.resume self digest = ok result := by
  exact match digest with
    | .None => ⟨_, rfl⟩
    | .Some value => (beacon_init_hash_some_exact self value).elim fun next facts => ⟨_, facts.1⟩

theorem BeaconMldsaSigning_resume_total (self : registration.BeaconMldsaSigning)
    (signature : core.option.Option (Slice Std.U8)) :
    ∃ result, registration.BeaconMldsaSigning.resume self signature = ok result := by
  exact match signature with
    | .None => ⟨_, rfl⟩
    | .Some value => (beacon_mldsa_signature_exact self value).imp fun _ facts => facts.1

end BeaconcryptCore.PanicFreedom.RegistrationSigningContinuations

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationSigningContinuations.begin_beacon_init_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationSigningContinuations.begin_beacon_init_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationSigningContinuations.BeaconFingerprint_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationSigningContinuations.BeaconFingerprint_resume_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationSigningContinuations.BeaconInitHash_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationSigningContinuations.BeaconInitHash_resume_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationSigningContinuations.BeaconMldsaSigning_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationSigningContinuations.BeaconMldsaSigning_resume_total

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySigningPair
import BeaconcryptCore.Computational.RegistrationNativeIdentityHashTemplate

/-! Actual Core fingerprint/hash continuations retain the one-time-field relation used by the real/censored source pair. The public fingerprint request is equal. A common actual Init-hash reply then produces identical ML requests; different retained raw Init preimages are not equated. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityHashPair
open BeaconcryptCore.Refinement
open RegistrationNativeIdentitySigningPair (stripState)

def Same (left right : registration.BeaconInitHash) : Prop :=
  stripState left.state = stripState right.state ∧ left.fingerprint = right.fingerprint

/-- The literal source public-key fingerprint request does not read attached one-time bytes. -/
theorem fingerprint_request (left right : registration.BeaconFingerprint)
    (same : stripState left.state = stripState right.state) : left.request = right.request := by
  calc
    _ = (⟨stripState left.state⟩ : registration.BeaconFingerprint).request := rfl
    _ = (⟨stripState right.state⟩ : registration.BeaconFingerprint).request :=
      congrArg (fun state => (⟨state⟩ : registration.BeaconFingerprint).request) same
    _ = _ := rfl

/-- Every common actual fingerprint reply reaches a pair with the same fingerprint and all other retained source fields outside the one-time attachment. -/
theorem fingerprint (left right : registration.BeaconFingerprint)
    (same : stripState left.state = stripState right.state) (digest : Std.Array U8 64#usize) :
    ∃ nextLeft nextRight,
      left.resume (.Some digest) = .ok (.HashRequested nextLeft) ∧
      right.resume (.Some digest) = .ok (.HashRequested nextRight) ∧ Same nextLeft nextRight := by
  obtain ⟨nextLeft, resumedLeft, stateLeft, fingerprintLeft, _⟩ := RegistrationSigningContinuations.beacon_fingerprint_some_exact left digest
  obtain ⟨nextRight, resumedRight, stateRight, fingerprintRight, _⟩ := RegistrationSigningContinuations.beacon_fingerprint_some_exact right digest
  exact ⟨nextLeft, nextRight, resumedLeft, resumedRight,
    by simpa only [Same, stateLeft, stateRight, fingerprintLeft, fingerprintRight, and_true] using same⟩

/-- The common actual transcript-hash reply computes the same source ML input. This uses the original builder/resume body, not an assumed request/source-game equality. -/
theorem hash (left right : registration.BeaconInitHash) (same : Same left right) (digest : Std.Array U8 64#usize) :
    ∃ nextLeft nextRight,
      left.resume (.Some digest) = .ok (.MldsaSigningRequested nextLeft) ∧
      right.resume (.Some digest) = .ok (.MldsaSigningRequested nextRight) ∧
      RegistrationNativeIdentitySigningPair.Same nextLeft nextRight := by
  obtain ⟨input, built, _⟩ := TranscriptAuthInputsRefinement.build_signature_input_abs .Beacon digest
  let nextLeft : registration.BeaconMldsaSigning := ⟨left.state, left.fingerprint, digest, input⟩
  let nextRight : registration.BeaconMldsaSigning := ⟨right.state, right.fingerprint, digest, input⟩
  refine ⟨nextLeft, nextRight, ?_, ?_, ?_⟩
  · simp only [registration.BeaconInitHash.resume, built, bind_tc_ok]
    rfl
  · simp only [registration.BeaconInitHash.resume, built, bind_tc_ok]
    rfl
  · simp only [RegistrationNativeIdentitySigningPair.Same, RegistrationNativeIdentitySigningPair.strip,
      nextLeft, nextRight, same.1, same.2]

end BeaconcryptCore.Computational.RegistrationNativeIdentityHashPair
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHashPair.fingerprint_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHashPair.fingerprint_request
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHashPair.fingerprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHashPair.fingerprint
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHashPair.hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHashPair.hash

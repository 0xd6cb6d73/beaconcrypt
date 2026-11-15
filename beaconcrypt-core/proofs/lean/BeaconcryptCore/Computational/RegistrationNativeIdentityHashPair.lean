-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentitySigningPair
import BeaconcryptCore.Computational.RegistrationNativeIdentityHashTemplate

/-! Actual request-hash continuations retain the one-time-field relation used by the real/censored Ed source pair. A common internal hash reply enters current Ready publication with the same original control; different retained raw Init preimages are not equated. -/
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
  stripState left.state = stripState right.state

/-- The common request-hash reply enters actual Ready publication with the same original control. -/
theorem hash (left right : registration.BeaconInitHash) (same : Same left right) (digest : Std.Array U8 64#usize) :
    ∃ nextLeft nextRight,
      left.resume (.Some digest) = .ok (.Ready nextLeft) ∧
      right.resume (.Some digest) = .ok (.Ready nextRight) ∧
      nextLeft.state.original_control = nextRight.state.original_control := by
  obtain ⟨nextLeft, resumedLeft, stateLeft, _hashLeft, _⟩ := RegistrationSigningContinuations.beacon_init_hash_some_exact left digest
  obtain ⟨nextRight, resumedRight, stateRight, _hashRight, _⟩ := RegistrationSigningContinuations.beacon_init_hash_some_exact right digest
  refine ⟨nextLeft, nextRight, resumedLeft, resumedRight, ?_⟩
  rw [stateLeft,stateRight]
  have controls : (stripState left.state).original_control = (stripState right.state).original_control :=
    congrArg registration.BeaconInitState.original_control same
  exact controls

end BeaconcryptCore.Computational.RegistrationNativeIdentityHashPair
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHashPair.hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHashPair.hash

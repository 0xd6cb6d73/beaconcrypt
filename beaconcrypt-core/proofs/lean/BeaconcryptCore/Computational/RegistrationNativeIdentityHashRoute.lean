-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityHashPair

/-! Within the literal Init publication controller, the attached-signature Init hash has its current source-fixed width. Only this internal publication subcall uses the classifier; unrelated public or trusted hash calls remain ordinary public-address queries. The classifier never needs the suppressed signature or its physical hash address. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityHashRoute
open BeaconcryptCore.Refinement

/-- The opaque token represents this controller's full attached-signature Init address. -/
def route (bytes : Pqxdh.Bytes) : Option Pqxdh.Bytes :=
  if bytes.length = 3543 then none else some bytes

/-- Every actual retained Init-hash request has width3543 and uses the same token, regardless of the attached one-time bytes. -/
theorem transcript (pending : registration.BeaconInitHash) :
    ∃ request, pending.request = .ok request ∧ RegistrationInputs.hashBytes request = absBytes pending.input ∧
      route (RegistrationInputs.hashBytes request) = none := by
  refine ⟨.Single pending.input.to_slice, rfl, rfl, ?_⟩
  change route (absBytes pending.input) = none
  simp only [route, absBytes_length]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeIdentityHashRoute

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityHashRoute.transcript' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityHashRoute.transcript

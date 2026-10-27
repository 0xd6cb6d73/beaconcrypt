-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationResponse

/-! Incoming response authentication returns normally on all represented packets and primitive replies. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core

set_option autoImplicit false

namespace BeaconcryptCore.PanicFreedom.RegistrationResponse

open BeaconcryptCore.Refinement.RegistrationResponse

theorem begin_response_authentication_total (pending : registration.BeaconPending)
    (packet : core.option.Option registration.ResponsePacket) :
    ∃ result, registration.begin_response_authentication pending packet = ok result := by
  exact match packet with
    | .None => ⟨_, rfl⟩
    | .Some value => (begin_response_some_exact pending value).elim fun next facts => ⟨_, facts.1⟩

theorem ResponseHash_resume_total (self : registration.ResponseHash)
    (digest : core.option.Option (Array Std.U8 64#usize)) :
    ∃ result, registration.ResponseHash.resume self digest = ok result := by
  exact match digest with
    | .None => ⟨_, rfl⟩
    | .Some value => (response_hash_some_exact self value).elim fun next facts => ⟨_, facts.1⟩

end BeaconcryptCore.PanicFreedom.RegistrationResponse

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationResponse.begin_response_authentication_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationResponse.begin_response_authentication_total

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationResponse.ResponseHash_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationResponse.ResponseHash_resume_total

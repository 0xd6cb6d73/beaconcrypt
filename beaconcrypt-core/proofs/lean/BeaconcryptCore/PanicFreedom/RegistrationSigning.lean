-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationSigning

/-! Unconditional normal returns for the outbound signing phases, including rejected or malformed replies. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
open BeaconcryptCore.Refinement.RegistrationSigning
open BeaconcryptCore.Refinement.RegistrationInputs
open BeaconcryptCore.Refinement.RegistrationBytePrimitives

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BeaconcryptCore.PanicFreedom.RegistrationSigning

theorem ed_request_total (self : registration.BeaconEd25519Signing) :
    ∃ result, self.request = ok result :=
  (ed_request_exact self).imp (fun _ h => h.1)

theorem ed_resume_total (self : registration.BeaconEd25519Signing)
    (signed : core.option.Option (Slice Std.U8)) :
    ∃ result, self.resume signed = ok result :=
  (ed_resume_refines self signed).imp (fun _ h => h.1)

end BeaconcryptCore.PanicFreedom.RegistrationSigning

/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationSigning.ed_request_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationSigning.ed_request_total
/-- info: 'BeaconcryptCore.PanicFreedom.RegistrationSigning.ed_resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.PanicFreedom.RegistrationSigning.ed_resume_total

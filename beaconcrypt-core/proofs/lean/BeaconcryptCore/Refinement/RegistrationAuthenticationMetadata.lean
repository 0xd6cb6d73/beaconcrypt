-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationAuthenticationFlow

/-!
The current Init controller retains its exact Server pin and request-hash reply through all three classical checks. These operational facts have no enrollment or Beacon ML credential premise.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Refinement.RegistrationAuthenticationMetadata

open RegistrationAuthentication RegistrationInbound RegistrationAuthenticationFlow

/-- Successful admission retains the exact selected Server binding/key and the actual first hash reply. There is no fingerprint phase. -/
theorem accepted_metadata (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (events : List Event) (accepted : registration.AuthenticatedInit)
    (execution : Executes pin packet events (.Accepted accepted)) :
    accepted.binding.server_pin.binding = pin.binding ∧
      accepted.binding.server_pin.public_key = pin.public_key ∧
      events.head? = some (.hash (.Some accepted.binding.init_hash)) := by
  obtain ⟨selected, _, tail, recorded⟩ := accepted_request_provenance pin packet events accepted execution
  exact ⟨congrArg session.ServerAuthenticationPin.binding selected,
    congrArg session.ServerAuthenticationPin.public_key selected, by simp [recorded]⟩

/-- The accepted request digest is the exact first hash callback result. -/
theorem accepted_digest (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (events : List Event) (accepted : registration.AuthenticatedInit) (digest : Digest)
    (execution : Executes pin packet events (.Accepted accepted))
    (first : events.head? = some (.hash (.Some digest))) : accepted.binding.init_hash = digest := by
  simpa using (accepted_metadata pin packet events accepted execution).2.2.symm.trans first

end BeaconcryptCore.Refinement.RegistrationAuthenticationMetadata

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthenticationMetadata.accepted_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthenticationMetadata.accepted_metadata

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthenticationMetadata.accepted_digest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthenticationMetadata.accepted_digest

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationCredentialMetadata
import BeaconcryptCore.Computational.RegistrationAuthenticationExecution
import BeaconcryptCore.Computational.PqxdhHeadlineBridges

/-! The actual accepted credential receipt selects exactly the existing typed identity/prekey/one-time/PQ tuple parsed from the original packet. Source field assignment and final native validation supply this relation; it is not a new frontend premise. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 2048

namespace BeaconcryptCore.Computational.RegistrationCredentialBridge

open BeaconcryptCore.Refinement.RegistrationCredentialMetadata
open BeaconcryptCore.Refinement.RegistrationAuthenticationFlow
open PqxdhHeadlineBridges

attribute [local irreducible] RegistrationAuthenticationExecutor.execute registration.begin_init_authentication

def parsedPacket (packet : registration.InitPacket) :=
  parsedBytes (absBytes packet.identity_key) ((absBytes packet.pre_key).drop 64)
    ((absBytes packet.one_time_key).drop 64) ((absBytes packet.pq_key).drop 64)

theorem credential_parsed (packet : registration.InitPacket) (verified : pqxdh.VerifiedInitKex)
    (credential : Credential packet verified) : parsedPacket packet = some (typedVerified verified) := by
  obtain ⟨input, identity, pre, oneTime, pq, validated⟩ := credential
  have parsed := ((validate_init_kex_bridge input).2.1 verified).mp validated
  simpa only [parsedFields, parsedPacket, absBytes, identity, pre, oneTime, pq, List.map_drop] using parsed

theorem accepted_parsed (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (events : List Event) (accepted : registration.AuthenticatedInit)
    (execution : Executes pin packet events (.Accepted accepted)) :
    parsedPacket packet = some (typedVerified accepted.registration) := by
  exact credential_parsed packet accepted.registration (accepted_credential pin packet events accepted execution)

theorem interpreted_accepted_parsed {State : Type}
    (implementation : QueryImpl RegistrationAuthenticationExecutor.Spec (StateT State ProbComp))
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (events : List Event) (accepted : registration.AuthenticatedInit) (before after : State)
    (supported : (.ok (events, .Accepted accepted), after) ∈ support
      ((simulateQ implementation (RegistrationAuthenticationExecutor.begin pin packet)).run before)) :
    parsedPacket packet = some (typedVerified accepted.registration) := by
  exact accepted_parsed pin packet events accepted
    (RegistrationAuthenticationExecutor.simulated_begin_sound implementation pin packet events
      (.Accepted accepted) before after supported)

end BeaconcryptCore.Computational.RegistrationCredentialBridge

/-- info: 'BeaconcryptCore.Computational.RegistrationCredentialBridge.credential_parsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationCredentialBridge.credential_parsed
/-- info: 'BeaconcryptCore.Computational.RegistrationCredentialBridge.accepted_parsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationCredentialBridge.accepted_parsed
/-- info: 'BeaconcryptCore.Computational.RegistrationCredentialBridge.interpreted_accepted_parsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationCredentialBridge.interpreted_accepted_parsed

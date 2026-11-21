-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordRootMetadata
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerExecution

/-! The actual mutable-environment lowering preserves the public agreement of the same supported root continuation. This receipt connects the retained native completion token to its own collector before the later Word build. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRootMetadata
open RegistrationNativeSecretWordServerCollect (Input)
open RegistrationNativeSecretWordMessage (ServerReady)
open RegistrationNativeSecretWordInterface (LocalSpec prepare)
open RegistrationNativeSecretWordTargetServerExecution (Auxiliary lower)
variable {n : Nat} {KemSK : Type}

/-- The supported root continuation carries precisely its authenticated collector's public agreement. -/
theorem rooted (implementation : QueryImpl (LocalSpec n KemSK)
      (StateT (RegistrationNativeSecretWordInterpreter.State n KemSK) ProbComp))
    (binding : session.RegistrationBinding)
    (collected : Input registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding)
    (ready : ServerReady) (before after : Auxiliary n KemSK)
    (supported : (.ok (some ready), after) ∈ support
      ((lower implementation
        (StateT.lift (simulateQ prepare (RegistrationNativeSecretWordServerRoot.client binding collected)))).run before)) :
    ready.agreement = ⟨PqxdhServerClearedRoot.pending binding.server_pin.binding collected.plain, binding⟩ := by
  simp only [RegistrationNativeSecretWordTargetServerExecution.lower_run, StateT.run_lift,
    bind_pure_comp, simulateQ_map, StateT.run_map, Functor.map_map, support_map] at supported
  obtain ⟨result, reached, returned⟩ := supported
  have value : result.1 = .ok (some ready) := congrArg Prod.fst returned
  rcases result with ⟨reply, current⟩
  dsimp only at value
  subst reply
  rw [← QueryImpl.simulateQ_compose] at reached
  exact RegistrationNativeSecretWordRootMetadata.interpreted_agreement (implementation ∘ₛ prepare)
    binding collected ready before.2 current reached

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRootMetadata

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRootMetadata.rooted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRootMetadata.rooted

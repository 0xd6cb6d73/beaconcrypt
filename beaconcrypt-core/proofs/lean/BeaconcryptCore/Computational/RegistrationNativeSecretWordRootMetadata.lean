-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordServerRoot

/-! A successful actual symbolic Server root retains the collector's public agreement independently of the preparation reply. In particular, its completion token carries the original encapsulation ciphertext; only the separate opaque reference is prepared. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordRootMetadata
open RegistrationNativeSecretWordServerCollect (Input)
open RegistrationNativeSecretWordMessage (PrepareSpec ServerReady)
variable {Reader E Private : Type}

/-- Every successful native root stores its same collector and authenticated binding in the public agreement. -/
theorem agreement (binding : session.RegistrationBinding)
    (collected : Input Reader E PqxdhJointIdentity.PeerEncoding) (ready : ServerReady)
    (supported : .ok (some ready) ∈ support (RegistrationNativeSecretWordServerRoot.client binding collected)) :
    ready.agreement = ⟨PqxdhServerClearedRoot.pending binding.server_pin.binding collected.plain, binding⟩ := by
  classical
  simp only [RegistrationNativeSecretWordServerRoot.client] at supported
  split at supported
  · simp only [mem_support_pure_iff] at supported
    cases supported
  · simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
    obtain ⟨reference, _queried, returned⟩ := supported
    cases reference with
    | none => cases returned
    | some reference =>
        simp only [Option.map_some, RustM.ok.injEq, Option.some.injEq] at returned
        exact congrArg RegistrationNativeSecretWordMessage.ServerReady.agreement returned

/-- Interpreting arbitrary preparation effects preserves the same public agreement. -/
theorem interpreted_agreement (implementation : QueryImpl PrepareSpec (StateT Private ProbComp))
    (binding : session.RegistrationBinding) (collected : Input Reader E PqxdhJointIdentity.PeerEncoding)
    (ready : ServerReady) (before after : Private)
    (supported : (.ok (some ready), after) ∈ support
      ((simulateQ implementation (RegistrationNativeSecretWordServerRoot.client binding collected)).run before)) :
    ready.agreement = ⟨PqxdhServerClearedRoot.pending binding.server_pin.binding collected.plain, binding⟩ := by
  apply agreement binding collected ready
  apply OracleComp.support_simulateQ_run'_subset implementation _ before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst supported

end BeaconcryptCore.Computational.RegistrationNativeSecretWordRootMetadata

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordRootMetadata.agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordRootMetadata.agreement
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordRootMetadata.interpreted_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordRootMetadata.interpreted_agreement

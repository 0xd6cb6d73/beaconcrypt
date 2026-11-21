-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorStatefulSupport
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasCreate
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyBirth
import BeaconcryptCore.Computational.RegistrationNativeSecretWordKemEarlyKeys
/-! A source Word interpretation exposes only its individual preparation, genuine routed KEM and nonrouted KEM-frame receipts. The contract contains no source callback, roster alignment or security conclusion. Actual native birth and source prefix invariants are derived from these leaves separately, retaining arbitrary persistent World state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKem
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterface (Spec)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Private A : Type} {base : OracleSpec I}

def NoRouted : (Spec n KemSK).Domain → Prop
  | .inl (.inr (.inr _)) => False
  | _ => True

structure Contract (implementation : QueryImpl (Spec n KemSK) (StateT Private ProbComp))
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK)
    (input : Message → Option Key)
    (provider : QueryImpl (RegistrationNativeSecretWordKemInterface.Routed KemSK)
      (StateT (RegistrationNativeSecretWordKemProvider.State KemSK) ProbComp)) : Prop where
  prepare : ∀ message before result,
    result ∈ support ((implementation (.inl (.inl message))).run before) →
      result.1 = (input message).map (fun _ => message) ∧ kem result.2 = kem before
  routed : ∀ query before result,
    result ∈ support ((implementation (.inl (.inr (.inr query)))).run before) →
      (result.1,kem result.2) ∈ support ((provider query).run (kem before))
  quiet : ∀ query, NoRouted query → ∀ before result,
    result ∈ support ((implementation query).run before) → kem result.2 = kem before

variable (setup : Setup base KemSK) (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (implementation : QueryImpl (Spec n KemSK) (StateT Private ProbComp))
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK) (input : Message → Option Key)
variable (contract : Contract implementation kem input
  (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge))

include contract in
/-- Every nonbirth Word leaf retains the complete private key list under its genuine early KEM receipt. -/
theorem query_keys (query : (Spec n KemSK).Domain) (quiet : ¬RegistrationNativeSecretWordTargetPoolFrame.IsCreate query)
    (before : Private) (result : (Spec n KemSK).Range query × Private)
    (supported : result ∈ support ((implementation query).run before)) :
    (kem result.2).1.keys = (kem before).1.keys := by
  rcases query with (message | (message | common) | routed) | record
  · exact congrArg (fun state => state.1.keys) (contract.quiet (.inl (.inl message)) trivial before result supported)
  · exact congrArg (fun state => state.1.keys) (contract.quiet (.inl (.inr (.inl (.inl message)))) trivial before result supported)
  · exact congrArg (fun state => state.1.keys) (contract.quiet (.inl (.inr (.inl (.inr common)))) trivial before result supported)
  · have actual := contract.routed routed before result supported
    have free : ¬RegistrationNativeSecretWordKemEarlyKeys.Creates (KemSK := KemSK) routed := by
      rcases routed with (other | key) | pool | key
      · trivial
      · trivial
      · cases pool <;> exact quiet
      · trivial
    exact RegistrationNativeSecretWordKemEarlyKeys.noncreate_keys setup.baseImpl setup.kem selected pairs publicKey challenge routed free (kem before) (result.1,kem result.2) actual
  · exact congrArg (fun state => state.1.keys) (contract.quiet (.inr record) trivial before result supported)

include contract in
/-- An actual source continuation with no private birth retains every reached private row, independently of World replies. -/
theorem program_keys (work : OracleComp (Spec n KemSK) A)
    (bounded : work.IsQueryBoundP (RegistrationNativeSecretWordTargetPoolFrame.IsCreate (KemSK := KemSK)) 0)
    (before : Private) (result : A × Private)
    (supported : result ∈ support ((simulateQ implementation work).run before)) :
    (kem result.2).1.keys = (kem before).1.keys := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    rfl
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    obtain ⟨first,later⟩ := bounded
    have quiet := first.resolve_right (by omega)
    rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,called,continued⟩ := supported
    exact (ih middle.1 (by simpa using later middle.1) middle.2 result continued).trans
      (query_keys setup selected pairs publicKey challenge implementation kem input contract query quiet before middle called)

include contract in
/-- The individual source birth returns the old indexed row length, appends its genuine pair and retains the reached getter marker. -/
theorem create_step (before : Private) (result : (Nat × MlKem768PublicKey) × Private)
    (supported : result ∈ support ((implementation (.inl (.inr (.inr (.inr (.inl .create)))))).run before)) :
    ∃ pair, result.1 = ((kem before).1.keys.length,pair.1) ∧
      (kem result.2).1.keys = (kem before).1.keys ++ [pair] ∧ (kem result.2).2 = (kem before).2 := by
  exact RegistrationNativeSecretWordKemEarlyBirth.create_step setup.baseImpl setup.kem selected pairs publicKey challenge
    (kem before) (result.1,kem result.2) (contract.routed (.inr (.inl .create)) before result supported)

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKem

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKem.query_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKem.query_keys

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKem.program_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKem.program_keys

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKem.create_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKem.create_step

import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceKem
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCollectedAtom
/-! The same actual selected-handle decapsulation receipt is the challenge atom under the genuine early provider. The source interpreter is arbitrary persistent state satisfying the derived individual KEM/prepare contract. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerKem
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca
open RegistrationNativeSecretWord (Word Key)
open RegistrationNativeSecretWordMessage (Message)
variable {n : Nat} {I KemSK Private : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK) (input : Message → Option Key)
    (contract : RegistrationNativePlatformLorSourceKem.Contract implementation kem input
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge))
include contract

theorem decap_atom (before after : Private) (word : Word)
    (supported : (some word,after) ∈ support ((implementation
      (.inl (.inr (.inr (.inr (.inl (.decapsulate selected challenge))))))).run before)) : word = Word.atom := by
  have actual := contract.routed (.inr (.inl (.decapsulate selected challenge))) before (some word,after) supported
  cases found : (kem before).1.keys[selected]? with
  | none =>
    simp [RegistrationNativeSecretWordKemEarly.early,RegistrationNativeSecretWordKemProvider.ordinary,
      RegistrationNativeSecretWordKemProvider.pool,StateT.run,found] at actual
  | some pair =>
    simp [RegistrationNativeSecretWordKemEarly.early,RegistrationNativeSecretWordKemProvider.ordinary,
      RegistrationNativeSecretWordKemProvider.pool,StateT.run,found] at actual
    exact actual.1

theorem root_fields (authenticated : registration.AuthenticatedResponse)
    (pending : RegistrationNativeSecretWordBeaconPrepare.Prepared registration.AuthenticatedResponse)
    (ready : RegistrationNativeSecretWordMessage.BeaconReady) (before after : Private)
    (supported : (.ok (some ready),after) ∈ support
      ((simulateQ (implementation ∘ₛ RegistrationNativeSecretWordInterface.liftLocal false)
        (simulateQ RegistrationNativeSecretWordInterface.prepare
          (RegistrationNativeSecretWordBeaconRoot.client authenticated pending))).run before)) :
    ready.reference = RegistrationNativeSecretWordBeaconRoot.message pending ∧
      ∃ key, input ready.reference = some key := by
  simp only [RegistrationNativeSecretWordBeaconRoot.client,bind_pure_comp,simulateQ_map,
    simulateQ_spec_query,RegistrationNativeSecretWordInterface.prepare,StateT.run_map,support_map] at supported
  obtain ⟨⟨reply,reached⟩,called,equal⟩ := supported
  simp only [QueryImpl.apply_compose,RegistrationNativeSecretWordInterface.liftLocal,simulateQ_spec_query] at called
  have echo := (contract.prepare (RegistrationNativeSecretWordBeaconRoot.message pending) before (reply,reached) called).1
  cases formed : input (RegistrationNativeSecretWordBeaconRoot.message pending) with
  | none =>
    simp only [formed,Option.map_none] at echo
    rw [echo] at equal
    cases equal
  | some key =>
    simp only [formed,Option.map_some] at echo
    rw [echo] at equal
    simp only [Option.map_some,Prod.mk.injEq,RustM.ok.injEq,Option.some.injEq] at equal
    obtain ⟨rfl,rfl⟩ := equal
    exact ⟨rfl,key,formed⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerKem

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerKem.decap_atom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerKem.decap_atom

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerKem.root_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerKem.root_fields

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerKem
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealStateLift
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCollect
import BeaconcryptCore.Computational.RegistrationNativeSecretWordGenericLower
/-! Public-prefix and decapsulation receipts come from the literal ordered Beacon collector under arbitrary persistent source state. No real record-service support is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerCollect
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationNativeSecretWord (Word Key)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWordGenericLower (Auxiliary lower lower_run)
variable {n : Nat} {I KemSK Private : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK)
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
local notation "localImpl" => implementation ∘ₛ RegistrationNativeSecretWordInterface.liftLocal false
noncomputable def compiler : QueryImpl
    (RegistrationNativeSecretWordBeaconCollect.Spec Unit Unit Unit Unit registration.AuthenticatedResponse)
    (StateT (Auxiliary Private) ProbComp) := fun query =>
  lower localImpl (RegistrationNativeSecretWordBeaconCompiler.prefixImpl setup owner oneTime authenticated query)

private theorem lower_program {J A : Type} {queries : OracleSpec J}
    (inner : QueryImpl queries (StateT RegistrationServerReferenceCompiler.Environment
      (OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)))) (work : OracleComp queries A) :
    lower localImpl (simulateQ inner work) = simulateQ (fun query => lower localImpl (inner query)) work :=
  RegistrationNativePlatformLorIdealStateLift.simulate localImpl inner work

theorem collect_run :
    lower localImpl (RegistrationNativeSecretWordBeaconCompiler.collect setup owner oneTime authenticated) =
      simulateQ (compiler setup implementation owner oneTime authenticated)
        (RegistrationNativeSecretWordBeaconPrepare.prepare (completedBinding := authenticated.binding) authenticated.control () () () []) := by
  unfold RegistrationNativeSecretWordBeaconCompiler.collect
  exact lower_program implementation _ _

theorem header (before after : Auxiliary Private)
    (value : RegistrationNativeSecretWordBeaconPrefix.Header Unit registration.AuthenticatedResponse)
    (supported : (some value,after) ∈ support
      ((simulateQ (compiler setup implementation owner oneTime authenticated)
        (simulateQ RegistrationNativeSecretWordBeaconCollect.ordinary
          (RegistrationNativeSecretWordBeaconPrefix.beforeDecap (D := Unit) (K := Unit) () []))).run before)) :
    value.response=authenticated ∧ value.ciphertext=authenticated.packet.public.kem_cipher_text ∧
      value.server=authenticated.packet.public.identity_key ∧
      setup.source.crypto.xpkConv (absBytes value.server)=some (absBytes value.serverConverted) := by
  change (some value,after) ∈ support ((simulateQ
    (fun query => lower localImpl (RegistrationNativeSecretWordBeaconCompiler.prefixImpl setup owner oneTime authenticated query)) _).run before) at supported
  rw [←lower_program,lower_run,support_map] at supported
  obtain ⟨⟨⟨reply,env⟩,privateState⟩,called,equal⟩ := supported
  simp only [Prod.mk.injEq] at equal
  obtain ⟨rfl,rfl⟩ := equal
  apply RegistrationNativeSecretWordTargetOwnerPrefix.header setup owner oneTime authenticated before.1 env value
  apply support_simulateQ_run'_subset localImpl _ before.2
  rw [StateT.run'_eq,support_map]
  exact ⟨((some value,env),privateState),called,rfl⟩

private theorem map_apply {S A B : Type} (f : A → B) (work : StateT S ProbComp A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map _ _ _
variable (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK) (input : Message → Option Key)
    (contract : RegistrationNativePlatformLorSourceKem.Contract implementation kem input
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge))
include contract

theorem getter (before after : Auxiliary Private) (word : Word) (handle : owner.kemHandle=selected)
    (supported : (some word,after) ∈ support
      ((compiler setup implementation owner oneTime authenticated
        (.decapsulate (PqxdhAcceptedRegistration.ciphertextArray challenge) ())).run before)) : word=Word.atom := by
  simp only [compiler] at supported
  rw [lower_run] at supported
  simp only [RegistrationNativeSecretWordBeaconCompiler.prefixImpl,StateT.run,simulateQ_map,
    RegistrationNativeSecretWordInterface.localKem,simulateQ_spec_query,map_apply,Functor.map_map,support_map] at supported
  obtain ⟨⟨reply,privateState⟩,called,equal⟩ := supported
  have sameReply : reply=some word := congrArg Prod.fst equal
  apply RegistrationNativePlatformLorSourceOwnerKem.decap_atom setup selected pairs publicKey challenge implementation kem input contract before.2 privateState word
  rw [sameReply] at called
  simp only [QueryImpl.compose,RegistrationNativeSecretWordInterface.liftLocal,
    RegistrationNativeSecretWordInterface.routedKem,RegistrationNativeSecretWordInterface.route,simulateQ_spec_query] at called
  rw [handle,(PqxdhPhase2InputBytes.ciphertext_roundtrip (PqxdhAcceptedRegistration.ciphertextArray challenge) challenge).2] at called
  exact called

theorem collect_atom (before after : Auxiliary Private)
    (pending : RegistrationNativeSecretWordBeaconPrepare.Prepared registration.AuthenticatedResponse)
    (handle : owner.kemHandle=selected)
    (ciphertext : authenticated.packet.public.kem_cipher_text=PqxdhAcceptedRegistration.ciphertextArray challenge)
    (supported : (some pending,after) ∈ support
      ((lower localImpl (RegistrationNativeSecretWordBeaconCompiler.collect setup owner oneTime authenticated)).run before)) :
    pending.collected.kem=Word.atom ∧ pending.collected.plain.response=authenticated ∧
      pending.collected.plain.ciphertext=authenticated.packet.public.kem_cipher_text ∧
      pending.collected.plain.server=authenticated.packet.public.identity_key ∧
      setup.source.crypto.xpkConv (absBytes pending.collected.plain.server)=some (absBytes pending.collected.plain.serverConverted) ∧
      PqxdhPhase2DhMetadata.admitted (completedBinding := authenticated.binding) authenticated.control pending.collected.plain=some pending.metadata := by
  rw [collect_run] at supported
  simp only [RegistrationNativeSecretWordBeaconPrepare.prepare,simulateQ_bind,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨⟨collected,middle⟩,called,supported⟩ := supported
  cases collected with
  | none =>
    simp only [simulateQ_pure,StateT.run_pure,Option.bind_none,mem_support_pure_iff] at supported
    cases supported
  | some collected =>
    cases admitted : PqxdhPhase2DhMetadata.admitted (completedBinding := authenticated.binding) authenticated.control collected.plain with
    | none =>
      simp only [Option.bind_some,admitted,Option.map_none,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
      cases supported
    | some metadata =>
      simp only [Option.bind_some,admitted,Option.map_some,simulateQ_pure,StateT.run_pure,
        mem_support_pure_iff,Prod.mk.injEq,Option.some.injEq] at supported
      obtain ⟨rfl,rfl⟩ := supported
      obtain ⟨header,first,reached,prepared,getterCall,response,ciphertextField,server,converted⟩ :=
        RegistrationNativeSecretWordTargetOwnerCollectReceipt.receipt _ () () () [] before after collected called
      have actual := RegistrationNativePlatformLorSourceOwnerCollect.header setup implementation owner oneTime authenticated before first header prepared
      have headerCiphertext := actual.2.1.trans ciphertext
      have atom : collected.kem=Word.atom := by
        apply getter setup implementation owner oneTime authenticated selected pairs publicKey challenge kem input contract
          first reached collected.kem handle
        rw [←headerCiphertext]
        exact getterCall
      exact ⟨atom,response.trans actual.1,ciphertextField.trans actual.2.1,
        server.trans actual.2.2.1,by rw [server,converted];exact actual.2.2.2,admitted⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerCollect

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerCollect.collect_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerCollect.collect_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerCollect.header' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerCollect.header

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerCollect.getter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerCollect.getter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerCollect.collect_atom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerCollect.collect_atom

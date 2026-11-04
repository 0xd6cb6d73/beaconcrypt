-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAlignment
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePrefix
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceExecution
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPath
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCreate
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCounter
import BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetLedgerCounter
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasRoster
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateFrontend
/-! The literal new typed source preserves owner/private-KEM row association under a persistent Word interpreter satisfying only the individual KEM leaf contract. Constructor failures and all stateful source callbacks retain their own reached replies; public-key aliases remain allowed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBornKey
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetAlignment (Aligned)
open RegistrationNativeSecretWordTargetPublication (key)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform E Private A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))


variable (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
    (kem : Private → RegistrationNativeSecretWordKemProvider.State KemSK) (input : Message → Option Key)
    (contract : RegistrationNativePlatformLorSourceKem.Contract implementation kem input
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge))
abbrev State (source : RegistrationNativeMldsa.Source) (Platform Private : Type) :=
  RegistrationNativePlatformLorStatefulSupport.State (RegistrationNativePlatformSecretWordOrdinary.State source Platform) Private
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks canonical source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "typed" => RegistrationNativePlatformLorStatefulSupport.typed implementation controller


include contract in
/-- The actual complete raw execution retains the genuine reserved private prefix under its original source create allowance. -/
theorem full_prefix (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (before : State source Platform Private) (keysEmpty : (kem before.2).1.keys=[])
    (result : A × (RegistrationNativeLedger.State × State source Platform Private))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto canonical serverKeyId bounds typed mode work before)) :
    RegistrationNativePlatformLorSourcePrefix.Prefixed pairs kem result.2.2.2 ∧ (kem result.2.2.2).1.keys.length ≤ budget.create := by
  rw [RegistrationNativePlatformLorSourceExecution.full_run,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  have reservedPrefix := RegistrationNativePlatformLorSourcePrefix.run_prefix setup selected pairs publicKey challenge implementation kem input contract
    checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    serverKeyId bounds mode work budget bounded reserved before.1 before.2 keysEmpty reached called
  cases equal
  exact reservedPrefix

include contract in
/-- Every same-run final source owner has its exact genuine reserved row, literal private handle and displayed public key, without a key-injectivity premise. -/
theorem full_born_key (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (before : State source Platform Private) (ownersEmpty : before.1.1.beacons=[]) (keysEmpty : (kem before.2).1.keys=[])
    (result : A × (RegistrationNativeLedger.State × State source Platform Private))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto canonical serverKeyId bounds typed mode work before))
    (index : Nat) (owner : RegistrationNativePublicOwners.Owner source) (found : result.2.2.1.1.beacons[index]?=some owner) :
    ∃ pair, pairs[index]?=some pair ∧ owner.view.kemHandle=index ∧ owner.view.kemPublic=pair.1 := by
  have aligned := RegistrationNativePlatformLorSourceAlignment.initialized setup checks canonical source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer selected pairs publicKey challenge implementation kem input contract
    serverKeyId bounds mode work before ownersEmpty keysEmpty result supported
  obtain ⟨pair,privateAt,handle,sameKey⟩ := RegistrationNativeSecretWordTargetAlignment.owner result.2.2.1.1.beacons (kem result.2.2.2).1.keys aligned index owner found
  have prefixed := full_prefix setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer selected pairs publicKey challenge implementation kem input contract serverKeyId bounds mode work budget bounded reserved before keysEmpty result supported
  have earlier := (List.getElem?_eq_some_iff.mp privateAt).1
  rw [prefixed.1,List.getElem?_take,ite_eq_left earlier] at privateAt
  exact ⟨pair,privateAt,handle,sameKey⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBornKey

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBornKey.full_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBornKey.full_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBornKey.full_born_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBornKey.full_born_key

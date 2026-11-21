-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPoolPrefix
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment
/-! A final owner of the actual current source has its same indexed reserved private KEM pair. Both roster alignment and reservation provenance are derived from the current raw program and public create budget, including owners born after an earlier accepted packet. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetBornKey
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetAlignment (Aligned)
open RegistrationNativeSecretWordTargetPublication (key)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

open RegistrationNativePlatformSecretWordAliasAlignment (State)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n) setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside provider outer
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "typed" => RegistrationNativePlatformSecretWordExecution.typed (n := n) setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside provider outer controller




omit primitive in
private theorem prefix_lookup (keys : List (MlKem768PublicKey × KemSK))
    (prefixed : keys = pairs.take keys.length) (index : Nat) (pair : MlKem768PublicKey × KemSK)
    (found : keys[index]? = some pair) : pairs[index]? = some pair := by
  have earlier := (List.getElem?_eq_some_iff.mp found).1
  rw [prefixed, List.getElem?_take, ite_eq_left earlier] at found
  exact found

/-- Same-run final owner lookup derives its exact reserved row and retained public key; no association or public-key uniqueness premise is supplied. -/
theorem full_born_key (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (before : State n KemSK source Platform) (ownersEmpty : before.1.1.beacons = []) (keysEmpty : before.2.kem.1.keys = [])
    (result : A × (RegistrationNativeLedger.State × State n KemSK source Platform))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      serverKeyId bounds typed mode work before))
    (index : Nat) (owner : RegistrationNativePublicOwners.Owner source) (found : result.2.2.1.1.beacons[index]? = some owner) :
    ∃ pair, pairs[index]? = some pair ∧ owner.view.kemHandle = index ∧ owner.view.kemPublic = pair.1 := by
  have aligned := RegistrationNativePlatformSecretWordAliasAlignment.initialized setup checks
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source route sign input inside selected pairs publicKey challenge outer
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    serverKeyId bounds mode work before ownersEmpty keysEmpty result supported
  obtain ⟨pair, privateAt, handle, sameKey⟩ := RegistrationNativeSecretWordTargetAlignment.owner
    result.2.2.1.1.beacons result.2.2.2.kem.1.keys aligned index owner found
  have prefixed := RegistrationNativePlatformSecretWordTargetPoolPrefix.full_prefix setup checks wire source route sign input inside selected pairs publicKey challenge outer
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    serverKeyId bounds mode work budget bounded reserved before keysEmpty result supported
  exact ⟨pair, prefix_lookup pairs result.2.2.2.kem.1.keys prefixed.1 index pair privateAt, handle, sameKey⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetBornKey

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetBornKey.full_born_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetBornKey.full_born_key

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAlignment
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRoster
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCreate
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCounter
import BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetLedgerCounter
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasRoster
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateFrontend
/-! Literal constructor shape and nonbirth metadata preservation derive the ordered public KEM roster prefix under any persistent source interpretation satisfying the individual KEM leaf contract. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRoster
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
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "typed" => RegistrationNativePlatformLorStatefulSupport.typed implementation controller

open RegistrationNativeSecretWordTargetRoster (Prefix)

omit primitive in
private theorem reflexive (owners : RegistrationNativePublicOwners.State source) : Prefix owners owners :=
  ⟨[], (List.append_nil _).symm⟩
omit primitive in
private theorem transitive (first middle last : RegistrationNativePublicOwners.State source)
    (earlier : Prefix first middle) (later : Prefix middle last) : Prefix first last := by
  obtain ⟨left, old⟩ := earlier
  obtain ⟨right, current⟩ := later
  exact ⟨left ++ right, by rw [current, old, List.append_assoc]⟩

omit primitive in
private theorem create_of_kind (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (created : RegistrationNativeRawAdapter.kind query = 1) :
    ∃ edPin mlPin keyId, query = .inr (.create edPin mlPin keyId) := by
  cases query with
  | inl coin => cases created
  | inr command => cases command <;> first | exact ⟨_, _, _, rfl⟩ | cases created

include contract in
/-- Each current typed source call retains every earlier owner tuple; creation only appends its actual new row. -/
theorem typed_prefix (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State source Platform Private) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source Platform Private)
    (supported : result ∈ support ((typed query).run before)) :
    Prefix before.1.1.beacons result.2.1.1.beacons := by
  by_cases created : RegistrationNativeRawAdapter.kind query = 1
  · obtain ⟨edPin, mlPin, keyId, rfl⟩ := create_of_kind query created
    rcases RegistrationNativePlatformLorSourceCreate.create_shape implementation setup selectedOwner publicPrekey reserveFrame writer
      selected pairs publicKey challenge kem input contract edPin mlPin keyId before result supported with same | ⟨pair, _keys, owners⟩
    · exact ⟨[], by simpa only [List.append_nil] using same.2⟩
    · exact ⟨_, owners⟩
  · have same := RegistrationNativePlatformLorSourceAlignment.typed_metadata setup checks wire source sign
      selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation query created before result supported
    exact ⟨[], by simpa only [List.append_nil] using same⟩

include contract in
/-- Every adaptive typed prefix preserves the same earlier ordered metadata. -/
theorem program_prefix (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A)
    (before : State source Platform Private) (result : A × State source Platform Private)
    (supported : result ∈ support ((simulateQ typed work).run before)) :
    Prefix before.1.1.beacons result.2.1.1.beacons :=
  OracleComp.simulateQ_run_preserves_inv_of_query typed (fun current => Prefix before.1.1.beacons current.1.1.beacons)
    (fun query current prior next called => transitive source _ _ _ prior
      (typed_prefix setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer selected pairs publicKey challenge implementation kem input contract query current next called))
    work before (reflexive source before.1.1.beacons) result supported

include contract in
/-- Bounded decoding and every malformed or failed raw path retain that same roster prefix. -/
theorem raw_program_prefix (work : OracleComp RegistrationNativeInterface.Spec A)
    (before : State source Platform Private) (result : A × State source Platform Private)
    (supported : result ∈ support ((simulateQ (RegistrationNativeRawAdapter.handler wire typed) work).run before)) :
    Prefix before.1.1.beacons result.2.1.1.beacons := by
  rw [RegistrationNativeRawAdapter.program_native] at supported
  exact program_prefix setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer selected pairs publicKey challenge implementation kem input contract _ before result supported

include contract in
/-- Full original ledger steps preserve prior metadata through actual secrecy draws and internal native sends. -/
theorem full_step_prefix (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (query : RegistrationNativeInterface.FullSpec.Domain) (before : RegistrationNativeLedger.State × State source Platform Private)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State source Platform Private))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed query).run before)) :
    Prefix before.2.1.1.beacons result.2.2.1.1.beacons := by
  rw [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at supported
  obtain ⟨inner, called, rfl⟩ := supported
  exact raw_program_prefix setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer selected pairs publicKey challenge implementation kem input contract _ before.2 inner called

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRoster

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRoster.typed_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRoster.typed_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRoster.program_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRoster.program_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRoster.raw_program_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRoster.raw_program_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRoster.full_step_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceRoster.full_step_prefix

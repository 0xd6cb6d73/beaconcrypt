-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRoster
import BeaconcryptCore.Computational.RegistrationNativeFullCompiler
/-! The actual current common-state source preserves every prior owner handle/PQ tuple in roster order, through failed constructors and arbitrary later callbacks. Private provider state and persistent platform state are kept on the literal typed/raw/full execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetRoster
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
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n) setup wire route sign input inside provider outer
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "typed" => RegistrationNativePlatformSecretWordExecution.typed (n := n) setup wire route sign input inside provider outer controller


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

/-- Each current typed source call retains every earlier owner tuple; creation only appends its actual new row. -/
theorem typed_prefix (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State n KemSK source Platform) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source Platform)
    (supported : result ∈ support ((typed query).run before)) :
    Prefix before.1.1.beacons result.2.1.1.beacons := by
  by_cases created : RegistrationNativeRawAdapter.kind query = 1
  · obtain ⟨edPin, mlPin, keyId, rfl⟩ := create_of_kind query created
    rcases RegistrationNativePlatformSecretWordAliasCreate.create_shape setup wire route sign input inside selected pairs publicKey challenge outer
      selectedOwner publicPrekey reserveFrame writer edPin mlPin keyId before result supported with same | ⟨pair, _keys, owners⟩
    · exact ⟨[], by simpa only [List.append_nil] using same.2⟩
    · exact ⟨_, owners⟩
  · have same := RegistrationNativePlatformSecretWordAliasAlignment.typed_metadata setup checks wire source route sign input inside selected pairs publicKey challenge outer
      selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query created before result supported
    exact ⟨[], by simpa only [List.append_nil] using same⟩

/-- Every adaptive typed prefix preserves the same earlier ordered metadata. -/
theorem program_prefix (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A)
    (before : State n KemSK source Platform) (result : A × State n KemSK source Platform)
    (supported : result ∈ support ((simulateQ typed work).run before)) :
    Prefix before.1.1.beacons result.2.1.1.beacons :=
  OracleComp.simulateQ_run_preserves_inv_of_query typed (fun current => Prefix before.1.1.beacons current.1.1.beacons)
    (fun query current prior next called => transitive source _ _ _ prior
      (typed_prefix setup checks wire source route sign input inside selected pairs publicKey challenge outer
        selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query current next called))
    work before (reflexive source before.1.1.beacons) result supported

/-- Bounded decoding and every malformed or failed raw path retain that same roster prefix. -/
theorem raw_program_prefix (work : OracleComp RegistrationNativeInterface.Spec A)
    (before : State n KemSK source Platform) (result : A × State n KemSK source Platform)
    (supported : result ∈ support ((simulateQ (RegistrationNativeRawAdapter.handler wire typed) work).run before)) :
    Prefix before.1.1.beacons result.2.1.1.beacons := by
  rw [RegistrationNativeRawAdapter.program_native] at supported
  exact program_prefix setup checks wire source route sign input inside selected pairs publicKey challenge outer
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ before result supported

/-- Full original ledger steps preserve prior metadata through actual secrecy draws and internal native sends. -/
theorem full_step_prefix (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (query : RegistrationNativeInterface.FullSpec.Domain) (before : RegistrationNativeLedger.State × State n KemSK source Platform)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK source Platform))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed query).run before)) :
    Prefix before.2.1.1.beacons result.2.2.1.1.beacons := by
  rw [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at supported
  obtain ⟨inner, called, rfl⟩ := supported
  exact raw_program_prefix setup checks wire source route sign input inside selected pairs publicKey challenge outer
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ before.2 inner called

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetRoster

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetRoster.typed_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetRoster.typed_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetRoster.program_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetRoster.program_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetRoster.raw_program_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetRoster.raw_program_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetRoster.full_step_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetRoster.full_step_prefix

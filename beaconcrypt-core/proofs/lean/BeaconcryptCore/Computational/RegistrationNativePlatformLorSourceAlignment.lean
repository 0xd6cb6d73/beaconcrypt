-- SPDX-License-Identifier: 0BSD
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAlignment
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

include contract in
/-- The actual nonconstructor source callback retains every current private KEM row. -/
theorem typed_keys (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (quiet : RegistrationNativeRawAdapter.kind query ≠ 1)
    (before : State source Platform Private) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source Platform Private)
    (supported : result ∈ support ((typed query).run before)) :
    (kem result.2.2).1.keys = (kem before.2).1.keys := by
  rw [RegistrationNativePlatformLorStatefulSupport.typed_run,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  have free := RegistrationNativePlatformSecretWordNoCreateFrontend.handler_free (n := n) setup checks wire source sign
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query quiet before.1
  have retained := RegistrationNativePlatformLorSourceKem.program_keys setup selected pairs publicKey challenge implementation kem input contract _ free before.2 reached called
  cases equal
  exact retained

/-- Metadata preservation is derived on the literal source callback support under each persistent interpretation. -/
theorem typed_metadata (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (quiet : RegistrationNativeRawAdapter.kind query ≠ 1)
    (before : State source Platform Private) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source Platform Private)
    (supported : result ∈ support ((typed query).run before)) :
    result.2.1.1.beacons.map key = before.1.1.beacons.map key := by
  have original := RegistrationNativePlatformLorStatefulSupport.typed_support implementation controller query before result supported
  exact RegistrationNativePlatformSecretWordAliasRoster.handler_keys setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query quiet before.1 (result.1,result.2.1) original

/-- The actual parsed-attempt counter advances before all accept outcomes under any persistent Word interpretation. -/
theorem typed_counter (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State source Platform Private) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source Platform Private)
    (supported : result ∈ support ((typed query).run before)) :
    result.2.1.1.parsedAccepts = before.1.1.parsedAccepts + (RegistrationNativeSecretWordTargetCounter.isAccept query).toNat := by
  exact RegistrationNativePlatformSecretWordTargetCounter.handler_counter setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before.1 (result.1,result.2.1)
    (RegistrationNativePlatformLorStatefulSupport.typed_support implementation controller query before result supported)

omit primitive in
private theorem create_of_kind (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (created : RegistrationNativeRawAdapter.kind query = 1) :
    ∃ edPin mlPin keyId,query = .inr (.create edPin mlPin keyId) := by
  cases query with
  | inl coin => cases created
  | inr command => cases command <;> first | exact ⟨_,_,_,rfl⟩ | cases created

include contract in
/-- Literal source creation and nonbirth metadata frames derive row association at every supported current typed step. -/
theorem typed_keeps (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State source Platform Private) (prior : Aligned before.1.1.beacons (kem before.2).1.keys)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source Platform Private)
    (supported : result ∈ support ((typed query).run before)) :
    Aligned result.2.1.1.beacons (kem result.2.2).1.keys := by
  by_cases created : RegistrationNativeRawAdapter.kind query = 1
  · obtain ⟨edPin,mlPin,keyId,rfl⟩ := create_of_kind query created
    exact RegistrationNativePlatformLorSourceCreate.aligned implementation setup selectedOwner publicPrekey reserveFrame writer
      selected pairs publicKey challenge kem input contract edPin mlPin keyId before result prior supported
  · have keys := typed_keys setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer selected pairs publicKey challenge implementation kem input contract query created before result supported
    have metadata := typed_metadata setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation query created before result supported
    rw [keys]
    exact RegistrationNativeSecretWordTargetAlignment.same _ _ _ prior metadata

include contract in
/-- Adaptive typed execution preserves that same actual public/private row association. -/
theorem program_keeps (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A)
    (before : State source Platform Private) (prior : Aligned before.1.1.beacons (kem before.2).1.keys)
    (result : A × State source Platform Private) (supported : result ∈ support ((simulateQ typed work).run before)) :
    Aligned result.2.1.1.beacons (kem result.2.2).1.keys :=
  OracleComp.simulateQ_run_preserves_inv_of_query typed (fun current => Aligned current.1.1.beacons (kem current.2).1.keys)
    (fun query current valid next reached => typed_keeps setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer selected pairs publicKey challenge implementation kem input contract query current valid next reached)
    work before prior result supported

include contract in
/-- The literal full raw compiler retains row association and the original ledger on all modes and failed sends. -/
theorem run_keeps (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : State source Platform Private)
    (prior : Aligned before.1.1.beacons (kem before.2).1.keys)
    (result : A × (RegistrationNativeLedger.State × State source Platform Private))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before)) :
    Aligned result.2.2.1.1.beacons (kem result.2.2.2).1.keys := by
  rw [RegistrationNativeFullCompiler.compile_run,support_map] at supported
  obtain ⟨middle,called,equal⟩ := supported
  cases equal
  exact program_keeps setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer selected pairs publicKey challenge implementation kem input contract _ before prior middle called

include contract in
/-- Empty source owners and private rows initialize the actual full compiled association invariant. -/
theorem initialized (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : State source Platform Private)
    (ownersEmpty : before.1.1.beacons=[]) (keysEmpty : (kem before.2).1.keys=[])
    (result : A × (RegistrationNativeLedger.State × State source Platform Private))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before)) :
    Aligned result.2.2.1.1.beacons (kem result.2.2.2).1.keys := by
  apply run_keeps setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer selected pairs publicKey challenge implementation kem input contract serverKeyId bounds mode work before _ result supported
  rw [ownersEmpty,keysEmpty]
  exact RegistrationNativeSecretWordTargetAlignment.empty

include contract in
private theorem raw_keeps (work : OracleComp RegistrationNativeInterface.Spec A)
    (before : State source Platform Private) (result : A × State source Platform Private)
    (prior : Aligned before.1.1.beacons (kem before.2).1.keys)
    (supported : result ∈ support ((simulateQ (RegistrationNativeRawAdapter.handler wire typed) work).run before)) :
    Aligned result.2.1.1.beacons (kem result.2.2).1.keys := by
  rw [RegistrationNativeRawAdapter.program_native] at supported
  exact program_keeps setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer selected pairs publicKey challenge implementation kem input contract _ before prior result supported

include contract in
/-- Each original full-ledger callback retains the same private-row association through its actual raw source steps. -/
theorem full_step_keeps (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State source Platform Private)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State source Platform Private))
    (prior : Aligned before.2.1.1.beacons (kem before.2.2).1.keys)
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed query).run before)) :
    Aligned result.2.2.1.1.beacons (kem result.2.2.2).1.keys := by
  rw [RegistrationNativeFullCompiler.handler,RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run,support_map] at supported
  obtain ⟨inner,called,rfl⟩ := supported
  exact raw_keeps setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer selected pairs publicKey challenge implementation kem input contract _ before.2 inner prior called

include contract in
/-- Every actual original chronological prefix retains its derived owner/private-row association. -/
theorem path_keeps (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    {before after : RegistrationNativeLedger.State × State source Platform Private} {entries : List RegistrationNativeInterface.Entry}
    (actual : RegistrationNativeSecretWordTargetPath.Path
      (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed) before entries after)
    (prior : Aligned before.2.1.1.beacons (kem before.2.2).1.keys) :
    Aligned after.2.1.1.beacons (kem after.2.2).1.keys :=
  RegistrationNativeSecretWordTargetPath.preserves _ (fun current => Aligned current.2.1.1.beacons (kem current.2.2).1.keys)
    (fun query current next valid called => full_step_keeps setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer selected pairs publicKey challenge implementation kem input contract serverKeyId bounds query current next valid called) actual prior

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAlignment

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAlignment.typed_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAlignment.typed_keys

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAlignment.typed_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAlignment.typed_metadata

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAlignment.typed_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAlignment.typed_counter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAlignment.typed_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAlignment.typed_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAlignment.program_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAlignment.program_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAlignment.run_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAlignment.run_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAlignment.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAlignment.initialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAlignment.full_step_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAlignment.full_step_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAlignment.path_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAlignment.path_keeps

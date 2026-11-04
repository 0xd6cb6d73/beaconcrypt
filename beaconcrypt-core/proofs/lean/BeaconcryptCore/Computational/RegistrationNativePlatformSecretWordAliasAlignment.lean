-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasCreate
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasRoster
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateFrontend
/-! Actual new typed callbacks preserve the separately represented owner index, private KEM row and displayed public key. Constructor failure, stateful publication and assigned-ID completion are covered under the genuine early provider; public-key aliases are allowed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment
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

abbrev State (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) (Platform : Type) :=
  RegistrationNativePlatformSecretWordExecution.State (RegistrationNativePlatformSecretWordOrdinary.State source Platform) n KemSK
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n) setup wire route sign input inside provider outer
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "typed" => RegistrationNativePlatformSecretWordExecution.typed (n := n) setup wire route sign input inside provider outer controller

/-- Actual nonconstructor typed calls retain every current private KEM pair. -/
theorem typed_keys (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (quiet : RegistrationNativeRawAdapter.kind query ≠ 1)
    (before : State n KemSK source Platform) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source Platform)
    (supported : result ∈ support ((typed query).run before)) :
    result.2.2.kem.1.keys = before.2.kem.1.keys := by
  rw [RegistrationNativePlatformSecretWordExecution.typed_run, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  have free := RegistrationNativePlatformSecretWordNoCreateFrontend.handler_free (n := n) setup checks wire source sign
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query quiet before.1
  have retained := RegistrationNativeSecretWordTargetPoolFrame.program_keys setup wire route sign input inside
    selected pairs publicKey challenge outer _ free before.2 reached called
  cases equal
  exact retained

/-- The genuine typed interpreter retains the literal free source roster metadata. -/
theorem typed_metadata (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (quiet : RegistrationNativeRawAdapter.kind query ≠ 1)
    (before : State n KemSK source Platform) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source Platform)
    (supported : result ∈ support ((typed query).run before)) :
    result.2.1.1.beacons.map key = before.1.1.beacons.map key := by
  have original := RegistrationNativePlatformSecretWordExecution.typed_support setup wire route sign input inside provider outer controller query before result supported
  exact RegistrationNativePlatformSecretWordAliasRoster.handler_keys setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query quiet before.1 (result.1, result.2.1) original

omit primitive in
private theorem create_of_kind (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (created : RegistrationNativeRawAdapter.kind query = 1) :
    ∃ edPin mlPin keyId, query = .inr (.create edPin mlPin keyId) := by
  cases query with
  | inl coin => cases created
  | inr command => cases command <;> first | exact ⟨_, _, _, rfl⟩ | cases created

/-- Every actual corrected typed callback derives current row alignment from its reached input alignment. -/
theorem typed_keeps (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State n KemSK source Platform) (prior : Aligned before.1.1.beacons before.2.kem.1.keys)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source Platform)
    (supported : result ∈ support ((typed query).run before)) :
    Aligned result.2.1.1.beacons result.2.2.kem.1.keys := by
  by_cases created : RegistrationNativeRawAdapter.kind query = 1
  · obtain ⟨edPin, mlPin, keyId, rfl⟩ := create_of_kind query created
    exact RegistrationNativePlatformSecretWordAliasCreate.aligned setup wire route sign input inside selected pairs publicKey challenge outer
      selectedOwner publicPrekey reserveFrame writer edPin mlPin keyId before result prior supported
  · have keys := typed_keys setup checks wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query created before result supported
    have metadata := typed_metadata setup checks wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query created before result supported
    rw [keys]
    exact RegistrationNativeSecretWordTargetAlignment.same _ _ _ prior metadata

/-- Arbitrary adaptive typed continuations preserve the same actual public/private row association. -/
theorem program_keeps (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A)
    (before : State n KemSK source Platform) (prior : Aligned before.1.1.beacons before.2.kem.1.keys)
    (result : A × State n KemSK source Platform)
    (supported : result ∈ support ((simulateQ typed work).run before)) :
    Aligned result.2.1.1.beacons result.2.2.kem.1.keys :=
  OracleComp.simulateQ_run_preserves_inv_of_query typed
    (fun current => Aligned current.1.1.beacons current.2.kem.1.keys)
    (fun query current valid next reached => typed_keeps setup checks wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query current valid next reached)
    work before prior result supported

/-- All-mode raw compilation retains alignment under the original full ledger, including secrecy draws and refused sends. -/
theorem run_keeps (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (before : State n KemSK source Platform) (prior : Aligned before.1.1.beacons before.2.kem.1.keys)
    (result : A × (RegistrationNativeLedger.State × State n KemSK source Platform))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before)) :
    Aligned result.2.2.1.1.beacons result.2.2.2.kem.1.keys := by
  rw [RegistrationNativeFullCompiler.compile_run, support_map] at supported
  obtain ⟨middle, called, equal⟩ := supported
  cases equal
  exact program_keeps setup checks wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ before prior middle called

/-- The actual empty public and private rosters initialize the full new raw alignment invariant. -/
theorem initialized (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (before : State n KemSK source Platform) (ownersEmpty : before.1.1.beacons = []) (keysEmpty : before.2.kem.1.keys = [])
    (result : A × (RegistrationNativeLedger.State × State n KemSK source Platform))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before)) :
    Aligned result.2.2.1.1.beacons result.2.2.2.kem.1.keys := by
  apply run_keeps setup checks wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before _ result supported
  rw [ownersEmpty, keysEmpty]
  exact RegistrationNativeSecretWordTargetAlignment.empty

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment.typed_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment.typed_keys

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment.typed_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment.typed_metadata

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment.typed_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment.typed_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment.program_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment.program_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment.run_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment.run_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment.initialized

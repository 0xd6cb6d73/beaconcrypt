import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinFrontend
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPath
-- SPDX-License-Identifier: 0BSD
/-! The current common-state Word source retains its stored Server pin through literal corrected accept/build, dynamic owner callbacks and ordinary record paths. The full original ledger prefix carries the same pin with all failure and persistent platform poststates retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetAlignment (Aligned)
open RegistrationNativeSecretWordTargetPath (Path)
open RegistrationNativeInterface (Entry)
open PqxdhKemIndCca
open PqxdhDeploymentTranscript (summarize)
variable {n : Nat} {I KemSK Platform E Value : Type} {base : OracleSpec I}
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
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "typed" => RegistrationNativePlatformSecretWordExecution.typed (n := n) setup wire route sign input inside provider outer controller

local notation "rawImpl" => RegistrationNativeRawAdapter.handler wire typed
/-- Interpreted current source callbacks retain their original stored Server pin and complete platform state. -/
theorem typed_pin (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK source Platform)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source Platform)
    (supported : result ∈ support ((typed query).run before)) :
    result.2.1.1.server.pin=before.1.1.server.pin :=
  RegistrationNativePlatformSecretWordServerPinFrontend.query setup checks wire sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before.1 (result.1,result.2.1)
    (RegistrationNativePlatformSecretWordExecution.typed_support setup wire route sign input inside provider outer controller query before result supported)

omit primitive in
private theorem program_preserves {Index : Type} {spec : OracleSpec Index}
    (implementation : QueryImpl spec (StateT (State n KemSK source Platform) ProbComp))
    (step : ∀ query before result, result ∈ support ((implementation query).run before) →
      result.2.1.1.server.pin = before.1.1.server.pin)
    (work : OracleComp spec Value) (before : State n KemSK source Platform) (result : Value × State n KemSK source Platform)
    (supported : result ∈ support ((simulateQ implementation work).run before)) :
    result.2.1.1.server.pin = before.1.1.server.pin := by
  apply OracleComp.simulateQ_run_preserves_inv_of_query implementation
    (fun current => current.1.1.server.pin = before.1.1.server.pin)
    (fun query current prior next reached => (step query current next reached).trans prior) work before _ result supported
  rfl

/-- Every raw adapter path retains the same Server authentication pin. -/
theorem raw (query : RegistrationNativeInterface.Spec.Domain) (before : State n KemSK source Platform)
    (result : RegistrationNativeInterface.Spec.Range query × State n KemSK source Platform)
    (supported : result ∈ support ((rawImpl query).run before)) :
    result.2.1.1.server.pin = before.1.1.server.pin := by
  exact program_preserves (source := source) typed
    (typed_pin setup checks wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
    (RegistrationNativeRawAdapter.adapter wire query) before result supported

/-- A complete original ledger callback preserves the Server pin, including secrecy coin/send programs. -/
theorem full (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State n KemSK source Platform)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK source Platform))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed query).run before)) :
    result.2.2.1.1.server.pin = before.2.1.1.server.pin := by
  rw [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at supported
  obtain ⟨reached, called, returned⟩ := supported
  cases returned
  exact program_preserves (source := source) rawImpl
    (raw setup checks wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
    _ before.2 reached called

/-- The same chronological original path retains its actual initial Server pin. -/
theorem path (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    {before after : RegistrationNativeLedger.State × State n KemSK source Platform}
    {entries : List RegistrationNativeInterface.Entry}
    (path : RegistrationNativeSecretWordTargetPath.Path
      (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed) before entries after) :
    after.2.1.1.server.pin = before.2.1.1.server.pin := by
  apply RegistrationNativeSecretWordTargetPath.preserves _
    (fun current => current.2.1.1.server.pin = before.2.1.1.server.pin)
    (fun query current result prior reached => (full setup checks wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        serverKeyId bounds query current result reached).trans prior) path
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinSource.typed_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinSource.typed_pin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinSource.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinSource.raw

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinSource.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinSource.full

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinSource.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordServerPinSource.path

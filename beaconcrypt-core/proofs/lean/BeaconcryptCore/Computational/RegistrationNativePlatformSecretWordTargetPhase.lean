-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCreateBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPhaseSyntax
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetLedgerCounter
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCounter
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPath
/-! The current full Word source consumes the early KEM reservation in exact birth order under its original public create allowance. The current source-derived constructor cap rules out fallback; no final-owner activation or private row association is supplied as a premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPhase
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



def Holds {source : RegistrationNativeMldsa.Source} (parsed : Nat) (state : State n KemSK source Platform) : Prop :=
  state.1.1.parsedAccepts ≤ parsed → state.2.kem.2 = none

/-- Every actual typed operation preserves the reached-prefix absent-marker invariant. -/
theorem typed_keeps (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State n KemSK source Platform) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source Platform)
    (prior : Holds selectedAccept before) (supported : result ∈ support ((typed query).run before)) :
    Holds selectedAccept result.2 := by
  intro below
  have counted := RegistrationNativePlatformSecretWordTargetLedgerCounter.typed_counter setup checks wire source route sign input inside selected pairs publicKey challenge outer
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before result supported
  have earlier : before.1.1.parsedAccepts ≤ selectedAccept := by omega
  have ordinary : ¬(RegistrationNativeSecretWordTargetCounter.isAccept query = true ∧ before.1.1.parsedAccepts = selectedAccept) := by
    rintro ⟨accepted, equal⟩
    rw [accepted, Bool.toNat_true, equal] at counted
    omega
  rw [RegistrationNativePlatformSecretWordExecution.typed_run, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  have unchanged := RegistrationNativeSecretWordTargetPhaseCore.program_phase setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside
    selected pairs publicKey challenge outer _
    (RegistrationNativePlatformSecretWordTargetPhaseSyntax.handler_free setup checks
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before.1 ordinary) before.2 reached called
  cases equal
  exact unchanged.trans (prior earlier)

/-- Arbitrary actual typed continuations retain the reached-prefix marker invariant. -/
theorem program_keeps (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A)
    (before : State n KemSK source Platform) (result : A × State n KemSK source Platform)
    (prior : Holds selectedAccept before) (supported : result ∈ support ((simulateQ typed work).run before)) :
    Holds selectedAccept result.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query typed (Holds selectedAccept)
    (fun query current valid next called => typed_keeps setup checks wire source route sign input inside selected pairs publicKey challenge outer
      selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query current next valid called) work before prior result supported

private theorem raw_keeps (work : OracleComp RegistrationNativeInterface.Spec A)
    (before : State n KemSK source Platform) (result : A × State n KemSK source Platform)
    (prior : Holds selectedAccept before)
    (supported : result ∈ support ((simulateQ (RegistrationNativeRawAdapter.handler (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) typed) work).run before)) :
    Holds selectedAccept result.2 := by
  rw [RegistrationNativeRawAdapter.program_native] at supported
  exact program_keeps setup checks wire source route sign input inside selected pairs publicKey challenge outer
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ before result prior supported

/-- The full original ledger step retains the same marker invariant below every real secrecy draw and refused send. -/
theorem full_step_keeps (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State n KemSK source Platform)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK source Platform))
    (prior : Holds selectedAccept before.2)
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds typed query).run before)) :
    Holds selectedAccept result.2.2 := by
  rw [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at supported
  obtain ⟨inner, called, rfl⟩ := supported
  exact raw_keeps setup checks wire source route sign input inside selected pairs publicKey challenge outer
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ before.2 inner prior called

/-- Every initialized actual original-ledger run derives this invariant from its literal absent provider marker. -/
theorem run_keeps (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (before : State n KemSK source Platform) (initialMarker : before.2.kem.2 = none)
    (result : A × (RegistrationNativeLedger.State × State n KemSK source Platform))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds typed mode work before)) :
    Holds selectedAccept result.2.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query
    (RegistrationNativeFullCompiler.handler setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds typed)
    (fun current => Holds selectedAccept current.2)
    (fun query current valid next called => full_step_keeps setup checks wire source route sign input inside selected pairs publicKey challenge outer
      selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds query current next valid called)
    _ (RegistrationNativeLedger.empty, before) (fun _ => initialMarker) result supported

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPhase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPhase.typed_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPhase.typed_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPhase.program_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPhase.program_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPhase.full_step_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPhase.full_step_keeps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPhase.run_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPhase.run_keeps

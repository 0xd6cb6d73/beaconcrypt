-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCreateBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment
import BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetLedgerCounter
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetLedgerCounter
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



/-- The current typed callback advances precisely on a parsed accept, preserving every platform and private-source result. -/
theorem typed_counter (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State n KemSK source Platform)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source Platform)
    (supported : result ∈ support ((typed query).run before)) :
    result.2.1.1.parsedAccepts = before.1.1.parsedAccepts + (RegistrationNativeSecretWordTargetCounter.isAccept query).toNat := by
  have free := RegistrationNativePlatformSecretWordExecution.typed_support setup
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside provider outer controller query before result supported
  exact RegistrationNativePlatformSecretWordTargetCounter.handler_counter setup checks
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before.1 (result.1,result.2.1) free

/-- Every full original ledger step retains the actual source counter-to-prefix equation. -/
theorem step_counter (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (query : RegistrationNativeInterface.FullSpec.Domain) (offset : Nat)
    (before : RegistrationNativeLedger.State × State n KemSK source Platform)
    (prior : before.2.1.1.parsedAccepts = offset + RegistrationNativeEvents.parsedAcceptCount
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) before.1.transcript)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK source Platform))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds typed query).run before)) :
    result.2.2.1.1.parsedAccepts = offset + RegistrationNativeEvents.parsedAcceptCount
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) result.2.1.transcript :=
  RegistrationNativeRegistrationTargetLedgerCounter.step_counter setup.source.crypto
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) typed (fun current => current.1.1.parsedAccepts)
    (typed_counter setup checks wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
    serverKeyId bounds query offset before prior result supported

/-- Every actual chronological source prefix derives its counter directly from the same complete ledger. -/
theorem path_counter (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (offset : Nat)
    {before after : RegistrationNativeLedger.State × State n KemSK source Platform}
    {entries : List RegistrationNativeInterface.Entry}
    (actual : RegistrationNativeSecretWordTargetPath.Path
      (RegistrationNativeFullCompiler.handler setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
        serverKeyId bounds typed) before entries after)
    (prior : before.2.1.1.parsedAccepts = offset + RegistrationNativeEvents.parsedAcceptCount
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) before.1.transcript) :
    after.2.1.1.parsedAccepts = offset + RegistrationNativeEvents.parsedAcceptCount
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) after.1.transcript :=
  RegistrationNativeSecretWordTargetPath.preserves _
    (fun current => current.2.1.1.parsedAccepts = offset + RegistrationNativeEvents.parsedAcceptCount
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) current.1.transcript)
    (fun query current next valid called => step_counter setup checks wire source route sign input inside selected pairs publicKey challenge outer
      selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      serverKeyId bounds query offset current valid next called) actual prior

/-- The original full raw run retains this exact equation without an initial zero-counter restriction. -/
theorem run_counter (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : State n KemSK source Platform)
    (result : A × (RegistrationNativeLedger.State × State n KemSK source Platform))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds typed mode work before)) :
    result.2.2.1.1.parsedAccepts = before.1.1.parsedAccepts + RegistrationNativeEvents.parsedAcceptCount
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) result.2.1.transcript :=
  OracleComp.simulateQ_run_preserves_inv_of_query _
    (fun current => current.2.1.1.parsedAccepts = before.1.1.parsedAccepts + RegistrationNativeEvents.parsedAcceptCount
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) current.1.transcript)
    (fun query current valid next called => step_counter setup checks wire source route sign input inside selected pairs publicKey challenge outer
      selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      serverKeyId bounds query before.1.1.parsedAccepts current valid next called)
    _ (RegistrationNativeLedger.empty,before)
    (by simp only [RegistrationNativeLedger.empty, RegistrationNativeEvents.parsedAcceptCount, List.filter_nil, List.length_nil, Nat.add_zero])
    result supported

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetLedgerCounter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetLedgerCounter.typed_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetLedgerCounter.typed_counter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetLedgerCounter.step_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetLedgerCounter.step_counter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetLedgerCounter.path_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetLedgerCounter.path_counter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetLedgerCounter.run_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetLedgerCounter.run_counter

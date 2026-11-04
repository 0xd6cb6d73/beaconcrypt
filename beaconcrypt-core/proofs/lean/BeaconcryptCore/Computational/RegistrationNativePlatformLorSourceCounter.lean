-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAlignment
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPath
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCreate
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCounter
import BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetLedgerCounter
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasRoster
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateFrontend
/-! The literal current parsed-accept counter equals the original native ledger scan at every full chronological prefix under any persistent Word interpretation. Counter increments are derived from free source bodies and exact raw compilation, including malformed packets and all callback failures. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCounter
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


variable (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
abbrev State (source : RegistrationNativeMldsa.Source) (Platform Private : Type) :=
  RegistrationNativePlatformLorStatefulSupport.State (RegistrationNativePlatformSecretWordOrdinary.State source Platform) Private
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "typed" => RegistrationNativePlatformLorStatefulSupport.typed implementation controller


/-- Every full source callback retains the exact original parsed-counter-to-ledger equation. -/
theorem step_counter (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (query : RegistrationNativeInterface.FullSpec.Domain) (offset : Nat)
    (before : RegistrationNativeLedger.State × State source Platform Private)
    (prior : before.2.1.1.parsedAccepts = offset + RegistrationNativeEvents.parsedAcceptCount wire before.1.transcript)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State source Platform Private))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed query).run before)) :
    result.2.2.1.1.parsedAccepts = offset + RegistrationNativeEvents.parsedAcceptCount wire result.2.1.transcript :=
  RegistrationNativeRegistrationTargetLedgerCounter.step_counter setup.source.crypto wire typed (fun current => current.1.1.parsedAccepts)
    (RegistrationNativePlatformLorSourceAlignment.typed_counter setup checks wire source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation)
    serverKeyId bounds query offset before prior result supported

/-- Every actual chronological prefix derives its source attempt ordinal from its same full original ledger. -/
theorem path_counter (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (offset : Nat)
    {before after : RegistrationNativeLedger.State × State source Platform Private} {entries : List RegistrationNativeInterface.Entry}
    (actual : RegistrationNativeSecretWordTargetPath.Path (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed) before entries after)
    (prior : before.2.1.1.parsedAccepts = offset + RegistrationNativeEvents.parsedAcceptCount wire before.1.transcript) :
    after.2.1.1.parsedAccepts = offset + RegistrationNativeEvents.parsedAcceptCount wire after.1.transcript :=
  RegistrationNativeSecretWordTargetPath.preserves _
    (fun current => current.2.1.1.parsedAccepts = offset + RegistrationNativeEvents.parsedAcceptCount wire current.1.transcript)
    (fun query current next valid called => step_counter setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation serverKeyId bounds query offset current valid next called) actual prior

/-- The literal original full raw run retains this exact source counter equation from any initial counter. -/
theorem run_counter (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : State source Platform Private)
    (result : A × (RegistrationNativeLedger.State × State source Platform Private))
    (supported : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds typed mode work before)) :
    result.2.2.1.1.parsedAccepts = before.1.1.parsedAccepts + RegistrationNativeEvents.parsedAcceptCount wire result.2.1.transcript :=
  OracleComp.simulateQ_run_preserves_inv_of_query _
    (fun current => current.2.1.1.parsedAccepts = before.1.1.parsedAccepts + RegistrationNativeEvents.parsedAcceptCount wire current.1.transcript)
    (fun query current valid next called => step_counter setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation serverKeyId bounds query before.1.1.parsedAccepts current valid next called)
    _ (RegistrationNativeLedger.empty,before)
    (by simp only [RegistrationNativeEvents.parsedAcceptCount,RegistrationNativeLedger.empty,List.filter_nil,List.length_nil,Nat.add_zero]) result supported

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCounter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCounter.step_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCounter.step_counter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCounter.path_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCounter.path_counter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCounter.run_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCounter.run_counter

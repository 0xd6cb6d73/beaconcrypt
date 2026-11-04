-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedLive
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedLiveCore
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedPlatform
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessions
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessionShape
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAcceptFrontend
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordSessionSlotsSource
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPath
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCreate
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCounter
import BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetLedgerCounter
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasRoster
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateFrontend
/-! Complete adaptive typed execution preserves the preparation of every surviving retained capability in the same chronological trace. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedProgram
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
local notation "actual" => RegistrationNativePlatformLorStatefulSupport.trace implementation
local notation "typed" => RegistrationNativePlatformLorStatefulSupport.typed actual controller


open RegistrationNativePlatformLorSourcePreparedTraceCore (Prepared)
local notation "Trace" => RegistrationNativeSecretWordFrontendTrace.State
attribute [local irreducible] RegistrationAuthenticationCompiler.program PqxdhDeploymentTranscript.acceptedKeys
  RegistrationNativePlatformServerReferenceAccept.pin
open RegistrationNativePlatformLorSourcePreparedLiveCore (Live)
variable (input : Message → Option Key)
    (echo : ∀ message before result,result∈support ((implementation (.inl (.inl message))).run before) →
      result.1=(input message).map (fun _=>message))
include echo in
/-- Complete adaptive typed source execution preserves the preparation of every surviving capability. -/
theorem program_live (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A)
    (before : State source Platform (Trace × Private)) (result : A × State source Platform (Trace × Private))
    (live : Live before.1.1.server before.2.1)
    (supported : result∈support ((simulateQ typed work).run before)) : Live result.2.1.1.server result.2.2.1 := by
  apply OracleComp.simulateQ_run_preserves_inv_of_query typed
    (fun current=>Live current.1.1.server current.2.1) ?_ work before _ result supported
  · intro query current prior next reached
    exact RegistrationNativePlatformLorSourcePreparedLive.typed_live setup checks wire source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation input echo query current next prior reached
  · exact live
end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedProgram
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedProgram.program_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedProgram.program_live

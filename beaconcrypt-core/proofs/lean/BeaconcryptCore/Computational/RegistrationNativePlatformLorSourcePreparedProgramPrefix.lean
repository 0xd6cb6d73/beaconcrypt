-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedLive
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedProgramCore
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
/-! The actual adaptive source prefix induction retains completed callback states and uses the proved live-table invariant before every later local material demand. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedProgramPrefix
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
open RegistrationNativePlatformOriginCallbackCut (Prefix)
local notation "WordSpec" => RegistrationNativeSecretWordInterface.Spec n KemSK
local notation "Front" => RegistrationNativePlatformSecretWordOrdinary.State source Platform
include echo in
/-- Adaptive source programs carry their actual completed callback state into every later literal demand prefix. -/
theorem program (stepPrepared : ∀ (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (front : Front) (before : Trace × Private)
    (message : Message) (tail : (WordSpec).Range (.inl (.inr (.inl (.inl message)))) →OracleComp WordSpec (RegistrationNativeRawAdapter.TypedSpec.Range query × Front))
    (after : Trace × Private), Live front.1.server before.1 →
    Prefix actual ((controller query).run front) before ((WordSpec).query (.inl (.inr (.inl (.inl message)))) >>=tail) after →Prepared message after.1)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A) (front : Front) (before : Trace × Private)
    (message : Message) (tail : (WordSpec).Range (.inl (.inr (.inl (.inl message)))) →OracleComp WordSpec (A × Front)) (after : Trace × Private)
    (live : Live front.1.server before.1)
    (path : Prefix actual ((simulateQ controller work).run front) before ((WordSpec).query (.inl (.inr (.inl (.inl message)))) >>=tail) after) :
    Prepared message after.1 := by
  apply RegistrationNativePlatformLorSourcePreparedProgramCore.program actual controller
    (fun front current=>Live front.1.server current.1) (fun descriptor current=>Prepared descriptor current.1)
    (fun descriptor=>.inl (.inr (.inl (.inl descriptor)))) ?_ stepPrepared work front before message tail after live path
  intro query current privateBefore value privateAfter called held
  have typedSupport : (value.1,(value.2,privateAfter))∈support ((typed query).run (current,privateBefore)) := by
    rw [RegistrationNativePlatformLorStatefulSupport.typed_run,support_map]
    exact ⟨(value,privateAfter),called,rfl⟩
  exact RegistrationNativePlatformLorSourcePreparedLive.typed_live setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation input echo query (current,privateBefore)
    (value.1,(value.2,privateAfter)) held typedSupport
end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedProgramPrefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedProgramPrefix.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedProgramPrefix.program

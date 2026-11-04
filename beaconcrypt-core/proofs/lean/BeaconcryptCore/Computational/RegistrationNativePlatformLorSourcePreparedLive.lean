-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTyped
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
/-! Every actual typed callback preserves the earlier preparation of every surviving Server capability, including failed operations and either routed accept branch. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedLive
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
/-- Actual typed source callbacks preserve the preparation of every surviving retained session. -/
theorem typed_live (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source Platform (Trace × Private))
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source Platform (Trace × Private))
    (live : Live before.1.1.server before.2.1)
    (supported : result∈support ((typed query).run before)) : Live result.2.1.1.server result.2.2.1 := by
  obtain ⟨added,appended⟩ := RegistrationNativePlatformLorSourcePreparedTyped.suffix setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation query before result supported
  have old := RegistrationNativePlatformLorSourcePreparedLiveCore.mono before.1.1.server before.2.1 result.2.2.1 added appended live
  have free := RegistrationNativePlatformLorStatefulSupport.typed_support actual controller query before result supported
  by_cases accepts : RegistrationNativeRawAdapter.kind query=3
  · cases query with
    | inl coin=>cases accepts
    | inr command=>cases command with
      | accept packet=>
        have shaped := supported
        rw [RegistrationNativePlatformLorSourceSessions.accept_run,support_map] at shaped
        obtain ⟨reached,called,equal⟩ := shaped
        have shape := RegistrationNativePlatformLorSourceSessionShape.accept _ setup checks _ source.verify packet
          (before.1.1.server,(before.1.1.environment,(before.1.2,before.2))) reached called
        have replyEq := congrArg Prod.fst equal
        have serverEq := congrArg (fun value=>value.2.1.1.server.sessions) equal
        change reached.1=result.1 at replyEq
        change reached.2.1.sessions=result.2.1.1.server.sessions at serverEq
        rw [replyEq,serverEq] at shape
        apply RegistrationNativePlatformLorSourcePreparedLiveCore.shape before.1.1.server result.2.1.1.server result.2.2.1 result.1 shape old
        intro handle returned
        have actualSupport : (.ok (some handle),result.2)∈support ((typed (.inr (.accept packet))).run before) := by
          rw [←returned]
          exact supported
        exact RegistrationNativePlatformLorSourcePreparedTyped.accept setup checks wire source sign selectedOwner selectedAccept publicPrekey
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation input echo packet before result.2 handle actualSupport
      | _=>cases accepts
  · by_cases builds : RegistrationNativeRawAdapter.kind query=4
    · cases query with
      | inl coin=>cases builds
      | inr command=>cases command with
        | build handle application=>
          have same := RegistrationNativePlatformSecretWordLiveBuild.sessions setup sign view failure allocation erased helper writer reservePeer
            source handle application before.1 (result.1,result.2.1) free
          have moved := (RegistrationNativePlatformLorSourcePreparedLiveCore.take handle before.1.1.server result.2.2.1 old).1
          intro ready member
          rw [same] at member
          exact moved ready member
        | _=>cases builds
    · have same := RegistrationNativePlatformSecretWordLiveState.quiet_server setup checks wire source sign selectedOwner selectedAccept publicPrekey
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query ⟨accepts,builds⟩ before.1 (result.1,result.2.1) free
      rw [same]
      exact old
end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedLive
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedLive.typed_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedLive.typed_live

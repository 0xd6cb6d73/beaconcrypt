-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedGenericAccept
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
/-! The actual typed controller retains its frontend, platform and chronological private state while exposing each successful accepted Ready and append-only trace. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTyped
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
/-- Every complete actual typed callback appends events in the same trace, including all refusal branches. -/
theorem suffix (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source Platform (Trace × Private))
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source Platform (Trace × Private))
    (supported : result∈support ((typed query).run before)) :
    ∃added,result.2.2.1.events=before.2.1.events++added := by
  rw [RegistrationNativePlatformLorStatefulSupport.typed_run,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  obtain ⟨added,appended⟩ := RegistrationNativePlatformLorSourcePreparedTraceCore.program_suffix implementation _ before.2 reached called
  have traceEq := congrArg (fun value=>value.2.2.1.events) equal
  change reached.2.1.events=result.2.2.1.events at traceEq
  exact ⟨added,traceEq.symm.trans appended⟩

variable (input : Message → Option Key)
    (echo : ∀ message before result,result∈support ((implementation (.inl (.inl message))).run before) →
      result.1=(input message).map (fun _=>message))
include echo in
/-- Every successful typed accept retains its own Ready prepared in its same actual returned trace. -/
theorem accept (packet : registration.InitPacket) (before after : State source Platform (Trace × Private)) (handle : Nat)
    (supported : (.ok (some handle),after)∈support ((typed (.inr (.accept packet))).run before)) :
    ∃ready : RegistrationNativeSecretWordMessage.ServerReady,
      after.1.1.server.sessions[handle]?=some (some ready) ∧Prepared ready.reference after.2.1 := by
  rw [RegistrationNativePlatformLorSourceSessions.accept_run,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  have replyEq : reached.1=.ok (some handle) := congrArg Prod.fst equal
  have recorded := RegistrationNativePlatformLorSourcePreparedPlatform.recorded (Platform := Platform) implementation
  have echoed := RegistrationNativePlatformLorSourcePreparedPlatform.echo_extended (Platform := Platform) implementation input echo
  have kept := RegistrationNativePlatformLorSourcePreparedGenericAccept.accept_prepared
    (RegistrationNativePlatformLorSourcePlatform.extend (Platform := Platform) actual) input (fun current=>current.2.1) recorded echoed
    setup checks (decide (before.1.1.parsedAccepts=selectedAccept))
    (RegistrationNativePlatformLorIdealStateLift.interpret actual (RegistrationNativePlatformSecretWordOrdinary.platform reserveRegistration))
    source.verify packet (before.1.1.server,(before.1.1.environment,(before.1.2,before.2))) reached.2 handle
    (by rw [←replyEq]; exact called)
  obtain ⟨ready,stored,prepared⟩ := kept
  have serverEq := congrArg (fun value=>value.2.1.1.server) equal
  have traceEq := congrArg (fun value=>value.2.2.1) equal
  change reached.2.1=after.1.1.server at serverEq
  change reached.2.2.2.2.1=after.2.1 at traceEq
  exact ⟨ready,by rw [←serverEq];exact stored,by rw [←traceEq];exact prepared⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTyped
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTyped.suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTyped.suffix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTyped.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTyped.accept

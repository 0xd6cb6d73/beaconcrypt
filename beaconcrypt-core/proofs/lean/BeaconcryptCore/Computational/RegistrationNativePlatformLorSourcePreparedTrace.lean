-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedProgramPrefix
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedDemand
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceBeaconPreparedPrefix
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTrace
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
omit primitive in
private theorem query_keeps (message : Message) (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain) (before : Trace × Private)
    (result : (RegistrationNativeSecretWordInterface.Spec n KemSK).Range query × (Trace × Private))
    (supported : result∈support ((actual query).run before)) (prepared : Prepared message before.1) : Prepared message result.2.1 := by
  exact RegistrationNativePlatformLorSourcePreparedTraceCore.prefix_keeps implementation message
    (show Prefix actual ((RegistrationNativeSecretWordInterface.Spec n KemSK).query query >>=fun _=>pure ()) before (pure ()) result.2 from .step .initial supported) prepared

include echo in
omit primitive in
private theorem traced_echo (message : Message) (before : Trace × Private)
    (result : Option Message × (Trace × Private))
    (supported : result∈support ((actual (.inl (.inl message))).run before)) :
    result.1=(input message).map (fun _=>message) :=
  echo message before.2 (result.1,result.2.2) (RegistrationNativePlatformLorSourceKemTrace.query_support implementation (.inl (.inl message)) before result supported)

include echo in
/-- Every demand inside an actual source callback has its own strictly earlier preparation in the same trace. -/
theorem query (current : RegistrationNativeRawAdapter.TypedSpec.Domain) (front : Front) (before after : Trace × Private)
    (message : Message) (tail : (WordSpec).Range (.inl (.inr (.inl (.inl message)))) →OracleComp WordSpec (RegistrationNativeRawAdapter.TypedSpec.Range current × Front))
    (live : Live front.1.server before.1)
    (path : Prefix actual ((controller current).run front) before ((WordSpec).query (.inl (.inr (.inl (.inl message)))) >>=tail) after) :
    Prepared message after.1 := by
  have noMaterial (quiet : ¬RegistrationNativePlatformSecretWordFrontendCaps.IsMaterial current) : Prepared message after.1 :=
    False.elim (RegistrationNativePlatformLorSourcePreparedDemand.quiet setup checks wire source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation current quiet front before after message tail path)
  cases current with
  | inl coin=>
    exact noMaterial (by simp only [RegistrationNativePlatformSecretWordFrontendCaps.IsMaterial,RegistrationNativeSecretWordFrontendCaps.IsMaterial,not_false_eq_true])
  | inr command=>cases command with
    | build handle application=>
      exact RegistrationNativePlatformLorSourcePreparedDemand.build setup source sign view failure allocation reservePeer erased helper writer implementation
        handle application front before after message tail live path
    | finish index packet=>
      exact RegistrationNativePlatformLorSourceBeaconPreparedPrefix.frontend actual Prod.fst (query_keeps implementation)
        setup input (traced_echo implementation input echo) (RegistrationNativePlatformLorSourcePreparedTraceCore.prepare_recorded implementation)
        wire source index packet front before after message tail path
    | _=>exact noMaterial (by simp only [RegistrationNativePlatformSecretWordFrontendCaps.IsMaterial,RegistrationNativeSecretWordFrontendCaps.IsMaterial,not_false_eq_true])

include echo in
/-- Any adaptive typed source prefix reaches its demand only after an actual earlier preparation of that descriptor. -/
theorem program (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A) (front : Front) (before after : Trace × Private)
    (message : Message) (tail : (WordSpec).Range (.inl (.inr (.inl (.inl message)))) →OracleComp WordSpec (A × Front))
    (live : Live front.1.server before.1)
    (path : Prefix actual ((simulateQ controller work).run front) before ((WordSpec).query (.inl (.inr (.inl (.inl message)))) >>=tail) after) :
    Prepared message after.1 :=
  RegistrationNativePlatformLorSourcePreparedProgramPrefix.program setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation input echo
    (fun current localFront start descriptor next finish held reached=>query setup checks wire source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation input echo current localFront start finish descriptor next held reached)
    work front before message tail after live path

include echo in
/-- Genuine cold Server sessions discharge the only initial live-table invariant internally. -/
theorem cold (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A) (front : Front) (before after : Trace × Private)
    (empty : front.1.server.sessions=[]) (message : Message)
    (tail : (WordSpec).Range (.inl (.inr (.inl (.inl message)))) →OracleComp WordSpec (A × Front))
    (path : Prefix actual ((simulateQ controller work).run front) before ((WordSpec).query (.inl (.inr (.inl (.inl message)))) >>=tail) after) :
    Prepared message after.1 := by
  apply program setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer implementation input echo work front before after message tail ?_ path
  intro ready member
  simp only [empty,List.not_mem_nil] at member
include echo in
/-- The original raw native client, including malformed inputs and its literal ledger compiler, derives every demand's strictly prior own preparation. -/
theorem raw (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (front : Front) (before after : Trace × Private)
    (empty : front.1.server.sessions=[]) (message : Message)
    (tail : (WordSpec).Range (.inl (.inr (.inl (.inl message)))) →OracleComp WordSpec ((A × RegistrationNativeLedger.State) × Front))
    (path : Prefix actual (RegistrationNativePlatformSecretWordFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front)
      before ((WordSpec).query (.inl (.inr (.inl (.inl message)))) >>=tail) after) : Prepared message after.1 :=
  cold setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation input echo
    (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds mode work)
    front before after empty message tail path
end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTrace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTrace.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTrace.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTrace.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTrace.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTrace.cold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTrace.cold

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTrace.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTrace.raw

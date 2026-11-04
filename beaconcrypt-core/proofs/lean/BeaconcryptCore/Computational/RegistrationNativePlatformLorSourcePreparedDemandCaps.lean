-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedTyped
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendCaps
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
/-! Static source bounds restrict each build to its already prepared moved descriptor and exclude material demands from all callbacks outside build and finish. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedDemandCaps
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
/-- The literal actual build tree only demands descriptors prepared at its own entry. -/
theorem build_bound (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform) (trace : Trace)
    (live : Live before.1.server trace) :
    ((RegistrationNativePlatformSecretWordFrontend.build (n := n) setup sign view failure allocation erased helper writer reservePeer
      handle application source).run before).IsQueryBoundP
      (RegistrationNativeSecretWordLiveCaps.Bad (KemSK := KemSK) (RegistrationNativePlatformLorSourcePreparedLiveCore.flags trace)) 0 := by
  simp only [RegistrationNativePlatformSecretWordFrontend.build,StateT.run,isQueryBoundP_map_iff]
  apply RegistrationNativePlatformSecretWordLiveBuildFree.embedded_free
  exact RegistrationNativePlatformSecretWordLiveBuildFree.body_free setup.source view failure allocation erased helper sign writer reservePeer
    (RegistrationNativePlatformLorSourcePreparedLiveCore.flags trace) handle application before.1.server (before.1.environment.receipts,before.2)
    (RegistrationNativePlatformLorSourcePreparedLiveCore.flags_live before.1.server trace live)

/-- All callbacks outside actual build/finish have zero material demands in their literal source tree. -/
theorem quiet_bound (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (quiet : ¬RegistrationNativePlatformSecretWordFrontendCaps.IsMaterial query)
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform) :
    ((controller query).run before).IsQueryBoundP (RegistrationNativeSecretWordFrontendCaps.IsDemand (KemSK := KemSK)) 0 := by
  have bounded := RegistrationNativePlatformSecretWordFrontendCaps.handler_bound (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before
  simpa only [ite_eq_right quiet] using bounded
end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedDemandCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedDemandCaps.build_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedDemandCaps.build_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedDemandCaps.quiet_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedDemandCaps.quiet_bound

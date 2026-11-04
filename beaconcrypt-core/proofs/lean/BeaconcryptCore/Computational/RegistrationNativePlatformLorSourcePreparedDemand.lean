-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedDemandCaps
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedPrefix
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
/-! Literal build prefixes use earlier preparations in their same reached trace; callbacks without material operations cannot reach a demand. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedDemand
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
open RegistrationNativePlatformOriginCallbackCut (Prefix)
/-- Every literal build demand uses an entry preparation that remains strictly in the past at the reached callback. -/
theorem build (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform) (privateBefore privateAfter : Trace × Private)
    (message : Message)
    (tail : (RegistrationNativeSecretWordInterface.Spec n KemSK).Range (.inl (.inr (.inl (.inl message)))) →
      OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) (RustM (Option (U64 × Pqxdh.Bytes)) × RegistrationNativePlatformSecretWordOrdinary.State source Platform))
    (live : Live before.1.server privateBefore.1)
    (path : Prefix actual ((RegistrationNativePlatformSecretWordFrontend.build (n := n) setup sign view failure allocation erased helper writer reservePeer
      handle application source).run before) privateBefore
      ((RegistrationNativeSecretWordInterface.Spec n KemSK).query (.inl (.inr (.inl (.inl message)))) >>=tail) privateAfter) :
    Prepared message privateAfter.1 := by
  classical
  have bounded := RegistrationNativePlatformLorSourcePreparedDemandCaps.build_bound (n := n) setup source sign view failure allocation reservePeer erased helper writer handle application before privateBefore.1 live
  have quiet := (isQueryBoundP_zero_iff _ (fun query=>¬RegistrationNativeSecretWordLiveCaps.Bad (KemSK := KemSK)
    (RegistrationNativePlatformLorSourcePreparedLiveCore.flags privateBefore.1) query)).mp (by simpa only [not_not] using bounded)
  have safe := RegistrationNativePlatformLorSourcePreparedPrefix.query_allowed actual _ _ quiet privateBefore _ tail privateAfter path
  change ¬RegistrationNativePlatformLorSourcePreparedLiveCore.flags privateBefore.1 message=false at safe
  have earlier : Prepared message privateBefore.1 := of_decide_eq_true (Bool.eq_true_of_not_eq_false safe)
  exact RegistrationNativePlatformLorSourcePreparedTraceCore.prefix_keeps implementation message path earlier

/-- A nonmaterial actual callback cannot reach a literal material demand at all. -/
theorem quiet (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (noMaterial : ¬RegistrationNativePlatformSecretWordFrontendCaps.IsMaterial query)
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform) (privateBefore privateAfter : Trace × Private)
    (message : Message)
    (tail : (RegistrationNativeSecretWordInterface.Spec n KemSK).Range (.inl (.inr (.inl (.inl message)))) →
      OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) (RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativePlatformSecretWordOrdinary.State source Platform))
    (path : Prefix actual ((controller query).run before) privateBefore
      ((RegistrationNativeSecretWordInterface.Spec n KemSK).query (.inl (.inr (.inl (.inl message)))) >>=tail) privateAfter) : False := by
  have bounded := RegistrationNativePlatformLorSourcePreparedDemandCaps.quiet_bound (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query noMaterial before
  have quietQueries := (isQueryBoundP_zero_iff _ (fun query=>¬RegistrationNativeSecretWordFrontendCaps.IsDemand (KemSK := KemSK) query)).mp
    (by simpa only [not_not] using bounded)
  have safe := RegistrationNativePlatformLorSourcePreparedPrefix.query_allowed actual _ _ quietQueries privateBefore _ tail privateAfter path
  exact safe trivial
end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedDemand
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedDemand.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedDemand.build
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedDemand.quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourcePreparedDemand.quiet

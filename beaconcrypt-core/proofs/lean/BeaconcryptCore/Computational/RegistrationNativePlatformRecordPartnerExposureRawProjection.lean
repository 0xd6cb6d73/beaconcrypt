-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClosedProjection
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedRun
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePrefixRewrite
/-! The original all-mode source frontend projects to the normalized opaque proxy through its own same-run preparation receipts. No callback, readiness, source-state or whole-security law is supplied by the caller. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRawProjection
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWordInterface (Spec)
open RegistrationNativePlatformOriginCallbackCut (Prefix)
open RegistrationNativePlatformRecordPartnerExposureExtract (Image)
open RegistrationNativePlatformRecordPartnerExposureDictionarySource (Ready)
variable {n : Nat} {I KemSK Physical Platform E A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (filler : PqxdhServerAuthKeySchedule.Output)
    (unused : QueryImpl RegistrationNativeSecretWordService.Combined (OracleComp (PqxdhRecordLiftInterface.WorldSpec n)))
    (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey ×KemSK))
    (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
    (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat →StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (front : RegistrationNativePlatformSecretWordOrdinary.State source Platform)
local notation "Current"=>RegistrationNativePlatformRecordPartnerExposureClosedProjection.Source n KemSK Physical
local notation "native"=>RegistrationNativePlatformLorCtxClosed.implementation setup wire sign seed scalar candidate unused selected pairs publicKey challenge physical
local notation "actual"=>RegistrationNativePlatformLorStatefulSupport.trace native
local notation "proxy"=>RegistrationNativePlatformRecordPartnerExposureClosedProjection.proxy setup wire sign seed scalar candidate filler selected pairs publicKey challenge physical
local notation "bare"=>RegistrationNativePlatformSecretWordFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front
local notation "Trace"=>RegistrationNativeSecretWordFrontendTrace.State

private theorem ready (before : Current) (empty : front.1.server.sessions=[])
    (request : (Spec n KemSK).Domain)
    (tail : (Spec n KemSK).Range request →OracleComp (Spec n KemSK)
      ((A ×RegistrationNativeLedger.State) ×RegistrationNativePlatformSecretWordOrdinary.State source Platform))
    (current : Trace ×Current)
    (path : Prefix actual bare (RegistrationNativeSecretWordFrontendTrace.initial,before)
      ((Spec n KemSK).query request >>=tail) current) : Ready setup seed scalar candidate request current.2.1.2 := by
  rcases request with (prepare|(demand|common)|kem)|record
  · trivial
  · intro available
    exact RegistrationNativePlatformRecordPartnerExposurePreparedRun.raw setup wire sign seed scalar candidate unused selected pairs publicKey challenge physical
      checks source selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      serverKeyId bounds mode work front before current empty demand available tail path
  · trivial
  · trivial
  · trivial

/-- The complete original source run uses only its internally prepared material queries in the same persistent physical execution. -/
theorem raw (before : Current) (empty : front.1.server.sessions=[]) (image : Image candidate before.1.2) :
    Prod.map id (RegistrationNativePlatformRecordPartnerExposureClosedProjection.traceProject candidate) <$>
      (simulateQ actual bare).run (RegistrationNativeSecretWordFrontendTrace.initial,before)=
    (simulateQ (RegistrationNativePlatformLorStatefulSupport.trace proxy) bare).run
      (RegistrationNativeSecretWordFrontendTrace.initial,RegistrationNativePlatformRecordPartnerExposureClosedProjection.project candidate before) := by
  apply RegistrationNativePlatformRecordPartnerExposurePrefixRewrite.map_run actual
    (RegistrationNativePlatformLorStatefulSupport.trace proxy)
    (RegistrationNativePlatformRecordPartnerExposureClosedProjection.traceProject candidate)
    (fun current=>Image candidate current.2.1.2) bare
    (RegistrationNativeSecretWordFrontendTrace.initial,before) image
  · intro request tail current path held
    exact RegistrationNativePlatformRecordPartnerExposureClosedProjection.trace_query setup wire sign seed scalar candidate filler unused selected pairs publicKey challenge physical
      request current held (ready setup wire sign seed scalar candidate unused selected pairs publicKey challenge physical checks source selectedOwner selectedAccept publicPrekey
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front before empty request tail current path)
  · intro request tail current result path held called
    exact RegistrationNativePlatformRecordPartnerExposureClosedProjection.trace_image setup wire sign seed scalar candidate filler unused selected pairs publicKey challenge physical
      request current held (ready setup wire sign seed scalar candidate unused selected pairs publicKey challenge physical checks source selectedOwner selectedAccept publicPrekey
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front before empty request tail current path) result called


/-- Genuine cold native address state discharges the source image internally while preserving its sampled44 table and known108 cache. -/
theorem cold (wordBefore : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (materials : (RegistrationNativePairedServices.MaterialSpec n).QueryCache)
    (known : RegistrationNativeSelectiveHiddenService.KnownOracle.QueryCache) (physicalBefore : Physical)
    (empty : front.1.server.sessions=[]) :
    Prod.map id (RegistrationNativePlatformRecordPartnerExposureClosedProjection.traceProject candidate) <$>
      (simulateQ actual bare).run (RegistrationNativeSecretWordFrontendTrace.initial,
        ((wordBefore,({RegistrationNativeHiddenService.initial with materials:=materials},known)),physicalBefore))=
    (simulateQ (RegistrationNativePlatformLorStatefulSupport.trace proxy) bare).run
      (RegistrationNativeSecretWordFrontendTrace.initial,
        ((wordBefore,(⟨fun _=>none,0,0,materials,known⟩ : RegistrationNativePlatformRecordPartnerExposureSlots.State n)),physicalBefore)) := by
  simpa only [RegistrationNativePlatformRecordPartnerExposureClosedProjection.project,
    RegistrationNativePlatformRecordPartnerExposureDictionarySource.project,
    RegistrationNativePlatformRecordPartnerExposureExtract.cold_extract] using
    raw setup wire sign seed scalar candidate filler unused selected pairs publicKey challenge physical checks source selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front
      ((wordBefore,({RegistrationNativeHiddenService.initial with materials:=materials},known)),physicalBefore)
      empty (RegistrationNativePlatformRecordPartnerExposureExtract.cold_image candidate materials known)

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRawProjection
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRawProjection.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRawProjection.raw

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRawProjection.cold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRawProjection.cold

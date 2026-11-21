-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureProxyBound
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureRawProjection
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientCaps
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendCaps
/-! The literal corrected raw source's installation exposure is charged to one candidate-independent executable recovery client, with genuine cold byte addresses and the same completed material table and reached physical state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureSourceBound
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

local notation "provider"=>RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "input"=>RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar
local notation "inside"=>RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))

include filler in
/-- Every actual source installation exposure on the same cold-address execution enters this client's literal recovery event. -/
theorem cold (wordBefore : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (materials : (RegistrationNativePairedServices.MaterialSpec n).QueryCache)
    (known : RegistrationNativeSelectiveHiddenService.KnownOracle.QueryCache) (physicalBefore : Physical)
    (empty : front.1.server.sessions=[]) :
    Pr{let result←(simulateQ actual bare).run (RegistrationNativeSecretWordFrontendTrace.initial,
      ((wordBefore,({RegistrationNativeHiddenService.initial with materials:=materials},known)),physicalBefore))}[
        RegistrationNativeSecretWordAliasExposureBound.Exposure input inside candidate result.2.1]≤
    Pr{let result←(RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate
      (RegistrationNativePlatformRecordPartnerExposureClient.client setup wire sign seed scalar provider physical bare
        RegistrationNativeSecretWordFrontendTrace.initial
          ((wordBefore,(⟨fun _=>none,0,0,materials,known⟩ : RegistrationNativePlatformRecordPartnerExposureSlots.State n)),physicalBefore)))}[
            candidate∈result.2.2] := by
  have exactSource := RegistrationNativePlatformRecordPartnerExposureRawProjection.cold setup wire sign seed scalar candidate filler unused
    selected pairs publicKey challenge physical checks source selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front
    wordBefore materials known physicalBefore empty
  have sameProbability :
    Pr{let result←(simulateQ actual bare).run (RegistrationNativeSecretWordFrontendTrace.initial,
      ((wordBefore,({RegistrationNativeHiddenService.initial with materials:=materials},known)),physicalBefore))}[
        RegistrationNativeSecretWordAliasExposureBound.Exposure input inside candidate result.2.1]=
    Pr{let result←(simulateQ (RegistrationNativePlatformLorStatefulSupport.trace proxy) bare).run (RegistrationNativeSecretWordFrontendTrace.initial,
        ((wordBefore,(⟨fun _=>none,0,0,materials,known⟩ : RegistrationNativePlatformRecordPartnerExposureSlots.State n)),physicalBefore))}[
          RegistrationNativeSecretWordAliasExposureBound.Exposure input inside candidate result.2.1] := by
    rw [←exactSource,prEvent_map]
    rfl
  exact sameProbability.le.trans (RegistrationNativePlatformRecordPartnerExposureProxyBound.fixed setup wire sign seed scalar
    candidate filler selected pairs publicKey challenge physical bare wordBefore
      (⟨fun _=>none,0,0,materials,known⟩ : RegistrationNativePlatformRecordPartnerExposureSlots.State n) physicalBefore)

/-- Both actual recovery bills follow from the original raw budget, with no caller material-cap premise. -/
theorem client_bound (wordBefore : RegistrationNativeSecretWordInterpreter.State n KemSK)
    (roots : RegistrationNativePlatformRecordPartnerExposureSlots.State n) (physicalBefore : Physical)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (kind : RegistrationNativeSecretWordServiceCaps.Kind) :
    (RegistrationNativePlatformRecordPartnerExposureClient.client setup wire sign seed scalar provider physical bare
      RegistrationNativeSecretWordFrontendTrace.initial ((wordBefore,roots),physicalBefore)).IsQueryBoundP
        (RegistrationNativeSecretWordServiceCaps.Counted kind) (budget.cap 4+budget.cap 5) := by
  apply RegistrationNativePlatformRecordPartnerExposureClientCaps.client_bound setup wire sign seed scalar provider physical bare _ _ _ _ kind
  exact (RegistrationNativePlatformSecretWordFrontendCaps.run_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work budget bounded front).of_imp
      (fun _ counted=>counted)

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureSourceBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureSourceBound.cold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureSourceBound.cold
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureSourceBound.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureSourceBound.client_bound

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePrepared
/-! The literal current raw source frontend derives its native prepared flag immediately before every valid material demand. Genuine source preparation is internal, and the same arbitrary reached physical state and completed material caches are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedRun
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWordInterface (Spec)
open RegistrationNativePlatformOriginCallbackCut (Prefix)
variable {n : Nat} {I KemSK Physical Platform E A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (unused : QueryImpl RegistrationNativeSecretWordService.Combined (OracleComp (PqxdhRecordLiftInterface.WorldSpec n)))
    (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey ×KemSK))
    (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
local notation "Input"=>RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar
local notation "Current"=>RegistrationNativePlatformLorCtxLeaves.Symbolic n KemSK ×Physical
local notation "impl"=>RegistrationNativePlatformLorCtxClosed.implementation setup wire sign seed scalar candidate unused selected pairs publicKey challenge physical
local notation "actual"=>RegistrationNativePlatformLorStatefulSupport.trace impl
local notation "Trace"=>RegistrationNativeSecretWordFrontendTrace.State

/-- The complete original raw client obtains its native preparation from its own earlier source callback on the same trace. -/
theorem raw (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat →StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (front : RegistrationNativePlatformSecretWordOrdinary.State source Platform) (before : Current) (after : Trace ×Current)
    (empty : front.1.server.sessions=[]) (message : Message) (available : (Input message).isSome=true)
    (tail : (Spec n KemSK).Range (.inl (.inr (.inl (.inl message)))) →OracleComp (Spec n KemSK)
      ((A ×RegistrationNativeLedger.State) ×RegistrationNativePlatformSecretWordOrdinary.State source Platform))
    (path : Prefix actual (RegistrationNativePlatformSecretWordFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work front)
      (RegistrationNativeSecretWordFrontendTrace.initial,before)
      ((Spec n KemSK).query (.inl (.inr (.inl (.inl message)))) >>=tail) after) :
    after.2.1.2.1.prepared (RegistrationNativeSecretWordMessage.eval candidate message)=true := by
  have contract := RegistrationNativePlatformLorCtxClosed.contract setup wire sign seed scalar candidate unused selected pairs publicKey challenge physical
  have echoed : ∀descriptor current result,result∈support ((impl (.inl (.inl descriptor))).run current) →
      result.1=(Input descriptor).map (fun _=>descriptor) := by
    intro descriptor current result called
    exact (contract.prepare descriptor current result called).1
  have prepared := RegistrationNativePlatformLorSourcePreparedTrace.raw setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer impl Input echoed
    serverKeyId bounds mode work front (RegistrationNativeSecretWordFrontendTrace.initial,before) after empty message tail path
  exact RegistrationNativePlatformRecordPartnerExposurePrepared.at_prefix setup wire sign seed scalar candidate unused selected pairs publicKey challenge physical
    _ before after _ path message available prepared

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedRun
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedRun.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposurePreparedRun.raw

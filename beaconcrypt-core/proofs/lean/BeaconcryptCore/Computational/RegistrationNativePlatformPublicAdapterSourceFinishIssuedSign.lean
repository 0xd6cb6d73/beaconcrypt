-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaOriginJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceSigningOrigin
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedJoint
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationAudit
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationReceipts
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedFinish
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceFinishIssuedSign
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
variable {n :Nat} {I KemSK P E R Error :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [primitives :AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [PublicWrapperPlatform.CryptoOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] [FrameDispatchFallback.Operations]
variable [originalGenerators :AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable [originalCrypto :CryptoOperations (RustT ProbComp)]
variable [originalLocal :LocalOperations (RustT (StateT P ProbComp))]
variable [originalContainers :ContainerOperations (RustT (StateT P ProbComp))]
variable {setup :PqxdhServerAuthExperiment.Setup base KemSK} {checks :PqxdhServerAuthExperiment.Checks}
variable (configuration :RegistrationNativePlatformPublicAdapterConfiguration.Configuration
  (P:=P) (E:=E) (R:=R) (Error:=Error) (source:=source) setup checks)
variable {Value :Type}
variable (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential :RegistrationNativeMldsa.Credential source)
local notation "Private"=>RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration created credential
local notation "physical"=>RegistrationNativePlatformPublicAdapterAuditLowModel.physical (n:=n) configuration created credential
local notation "Log"=>RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P

local notation "Stage"=>RegistrationNativePlatformPublicAdapterSourceTrace.Stage
open RegistrationNativePlatformPublicAdapterSourceEvents (Event)
local notation "receipts"=>RegistrationNativePlatformPublicAdapterSourceSigningHistory.receipts
local notation "stages"=>RegistrationNativePlatformPublicAdapterSourceAuthentication.stages
local notation "flag"=>RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.flag configuration.view credential.publicKey
local notation "model"=>RegistrationNativePlatformPublicAdapterAuditLowModel.model configuration created credential
local notation "State"=>RegistrationNativePlatformPublicAdapterLoggedJoint.State (n:=n) configuration created credential


omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
/-- The successful protected Finish trial has an actual same-key source signing request in its strict-before source history, outside the one native bad-call exception. -/
theorem sign (current:State)
    (held:RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback.Invariant configuration created credential current)
    (calls:List (RegistrationNativeStageTrace.Call RegistrationNativeRawAdapter.TypedSpec (RegistrationNativeExperiment.State n KemSK source×P)))
    (good:¬RegistrationNativePlatformOrdinaryMldsaOriginJournal.BadCalls credential calls)
    (index:Nat) (packet:registration.ResponsePacket) (application:Pqxdh.Bytes)
    (after:RegistrationNativeExperiment.State n KemSK source×P)
    (member:(⟨.inr (.finish index (some packet)),current.1.1.1,.ok (some application),after⟩:
      RegistrationNativeStageTrace.Call RegistrationNativeRawAdapter.TypedSpec (RegistrationNativeExperiment.State n KemSK source×P))∈calls)
    (owner:RegistrationNativeBeaconFrontend.Owner source) (pending:registration.BeaconPending) (scalar:PqxdhJointGapDh.ScalarBytes)
    (found:current.1.1.1.1.beacons[index]?=some owner) (phase:owner.phase=.initSent pending scalar)
    (key:pending.binding.server_pin.public_key=credential.publicKey) :
    ∃request digest reply,
      RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage
        (RegistrationNativePlatformPublicAdapterSourceTrace.Stage.sign request (RegistrationResponseExecutor.payload pending packet) digest reply)∈current.2 ∧
      request.public_key=credential.publicKey:=by
  have issued:=RegistrationNativePlatformOrdinaryMldsaOriginJournal.finish_issued credential calls good index packet application
    current.1.1.1 after member owner pending scalar found phase key
  have aligned:RegistrationNativePlatformPublicAdapterSourceSigningHistory.Aligned
      (RegistrationNativeMldsaShared.nativeProject current.1.1.1.1,stages current.2):=held.1
  have sameHistory:=RegistrationNativePlatformPublicAdapterSourceSigningHistory.history_eq
    (PqxdhRefinement.absBytes pending.binding.server_pin.public_key)
    (RegistrationNativeMldsaShared.nativeProject current.1.1.1.1,stages current.2) aligned
  rw [sameHistory] at issued
  obtain ⟨request,digest,reply,present,sameKey⟩:=RegistrationNativePlatformPublicAdapterSourceSigningOrigin.issued_sign
    (PqxdhRefinement.absBytes pending.binding.server_pin.public_key) true (stages current.2)
    (RegistrationResponseExecutor.payload pending packet) (PqxdhRefinement.absBytes packet.signature) issued
  have sourceKey:request.public_key=pending.binding.server_pin.public_key:=
    Subtype.ext ((PqxdhRefinement.absBytes_inj_iff _ _).mp sameKey)
  refine ⟨request,digest,reply,?_,sourceKey.trans key⟩
  obtain ⟨event,present,same⟩:=List.mem_filterMap.mp present
  cases event with
  | opened _ _ | closed _ _ _=>cases same
  | stage actual=>
    have actualEq:=Option.some.inj same
    cases actualEq
    exact present

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceFinishIssuedSign

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceFinishIssuedSign.sign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceFinishIssuedSign.sign

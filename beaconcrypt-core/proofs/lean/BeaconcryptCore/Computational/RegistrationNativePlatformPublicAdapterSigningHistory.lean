-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildSigningHistory
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSigningAligned
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigningAligned
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleLogSuffix
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedJoint
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSigningQuiet
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceSigningHistory
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthentication
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSigningHistory
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
variable (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
local notation "Private"=>RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration created credential
local notation "physical"=>RegistrationNativePlatformPublicAdapterAuditLowModel.physical (n:=n) configuration created credential
local notation "Log"=>RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P

local notation "Stage"=>RegistrationNativePlatformPublicAdapterSourceTrace.Stage
local notation "receipts"=>RegistrationNativePlatformPublicAdapterSourceSigningHistory.receipts
local notation "stages"=>RegistrationNativePlatformPublicAdapterSourceAuthentication.stages

local notation "Low"=>RegistrationNativePlatformPublicAdapterLowSpec.Spec
local notation "calls"=>RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential
local notation "augmentation"=>RegistrationNativePlatformPublicAdapterLoggedJoint.augmentation configuration created credential
local notation "model"=>RegistrationNativePlatformPublicAdapterAuditLowModel.model configuration created credential

omit [PublicWrapperPlatform.CryptoOperations] in
private theorem quiet_low (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain) (allowed :RegistrationNativePlatformPublicAdapterSigningQuiet.Quiet (RegistrationNativePlatformPublicAdapterLowSpec.nativeQuery query))
    (before :RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source)
    (result :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Range query×RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source)
    (supported :result∈support ((model query).run before)) :result.2.1.1.server.world.world.2=before.1.1.server.world.world.2 :=by
  cases query with
  | inl publicQuery=>
    have actual:=Eq.mp (congrArg (fun action=>result∈support (action.run before))
      (RegistrationNativePlatformPublicAdapterAuditLowModel.public_query configuration created credential publicQuery)) supported
    cases publicQuery with
    | inl coin=>exact RegistrationNativePlatformPublicAdapterSigningQuiet.raw configuration created credential (.inl coin) allowed before result actual
    | inr command=>exact RegistrationNativePlatformPublicAdapterSigningQuiet.raw configuration created credential (.inr (RegistrationNativePlatformPublicAdapterInterface.nativeCommand command)) allowed before result actual
  | inr refused=>cases refused with
    | serverSend key bytes oversized=>
      have actual:=Eq.mp (congrArg (fun action=>result∈support (action.run before))
        (RegistrationNativePlatformPublicAdapterAuditLowModel.server_query configuration created credential key bytes oversized)) supported
      exact RegistrationNativePlatformPublicAdapterSigningQuiet.raw configuration created credential (.inr (.serverSend key bytes)) allowed before result actual
    | beaconSend owner bytes oversized=>
      have actual:=Eq.mp (congrArg (fun action=>result∈support (action.run before))
        (RegistrationNativePlatformPublicAdapterAuditLowModel.beacon_query configuration created credential owner bytes oversized)) supported
      exact RegistrationNativePlatformPublicAdapterSigningQuiet.raw configuration created credential (.inr (.beaconSend owner bytes)) allowed before result actual

private theorem quiet_suffix (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain) (before :RegistrationNativePlatformExtractedSdkPublic.State Private) (prior :Log)
    (same :augmentation query before prior=RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged (calls query before.1 before.2) prior) :
    ∀result,result∈support (augmentation query before prior).sample→∃middle :List Stage,result.2=prior++middle.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage :=by
  rw [same]
  intro result supported
  exact ⟨[],by simpa using RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged_log _ prior ⟨result,supported⟩⟩

private theorem quiet_aligned (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain) (before :RegistrationNativePlatformExtractedSdkPublic.State Private) (prior :Log)
    (allowed :RegistrationNativePlatformPublicAdapterSigningQuiet.Quiet (RegistrationNativePlatformPublicAdapterLowSpec.nativeQuery query))
    (same :augmentation query before prior=RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged (calls query before.1 before.2) prior)
    (held :before.1.1.1.server.world.world.2=receipts (stages prior)) :
    ∀result,result∈support (augmentation query before prior).sample→
      ((calls query before.1 before.2).step.native result.1).2.1.1.server.world.world.2=receipts (stages result.2) :=by
  intro result supported
  let packet:{value //value∈support (augmentation query before prior).sample}:=⟨result,supported⟩
  have frame:=quiet_low configuration created credential query allowed before.1 ((calls query before.1 before.2).step.native result.1)
    (RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback.packet_native configuration created credential query before prior packet)
  have logEq:result.2=prior:=by
    have actual:=Eq.mp (congrArg (fun chosen=>result∈support chosen.sample) same) supported
    exact RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged_log _ prior ⟨result,actual⟩
  rw [logEq]
  exact frame.trans held

theorem suffix (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain) (before :RegistrationNativePlatformExtractedSdkPublic.State Private) (prior :Log) :
    ∀result,result∈support (augmentation query before prior).sample→∃middle :List Stage,result.2=prior++middle.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage :=by
  cases query with
  | inl publicQuery=>cases publicQuery with
    | inl coin=>exact quiet_suffix configuration created credential _ before prior rfl
    | inr command=>cases command with
      | bundle index=>exact RegistrationNativePlatformPublicAdapterBundleLogSuffix.suffix configuration created credential index (before.1.1.1,none) before.1.1.2 before.2 prior
      | build handle payload=>exact RegistrationNativePlatformPublicAdapterBuildSigningHistory.suffix configuration created credential handle payload before prior
      | finish index input=>exact RegistrationNativePlatformPublicAdapterFinishSigningAligned.suffix configuration created credential index input before prior
      | _=>exact quiet_suffix configuration created credential _ before prior rfl
  | inr refused=>cases refused <;>exact quiet_suffix configuration created credential _ before prior rfl

theorem aligned (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain) (before :RegistrationNativePlatformExtractedSdkPublic.State Private) (prior :Log)
    (held :before.1.1.1.server.world.world.2=receipts (stages prior)) :
    ∀result,result∈support (augmentation query before prior).sample→
      ((calls query before.1 before.2).step.native result.1).2.1.1.server.world.world.2=receipts (stages result.2) :=by
  cases query with
  | inl publicQuery=>cases publicQuery with
    | inl coin=>exact quiet_aligned configuration created credential _ before prior (by trivial) rfl held
    | inr command=>cases command with
      | bundle index=>exact RegistrationNativePlatformPublicAdapterBundleSigningAligned.aligned configuration created credential index (before.1.1.1,none) before.1.1.2 before.2 prior held
      | build handle payload=>exact RegistrationNativePlatformPublicAdapterBuildSigningHistory.aligned configuration created credential handle payload before prior held
      | finish index input=>exact RegistrationNativePlatformPublicAdapterFinishSigningAligned.aligned configuration created credential index input before prior held
      | _=>exact quiet_aligned configuration created credential _ before prior (by trivial) rfl held
  | inr refused=>cases refused <;>exact quiet_aligned configuration created credential _ before prior (by trivial) rfl held

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSigningHistory

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSigningHistory.suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSigningHistory.suffix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSigningHistory.aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSigningHistory.aligned

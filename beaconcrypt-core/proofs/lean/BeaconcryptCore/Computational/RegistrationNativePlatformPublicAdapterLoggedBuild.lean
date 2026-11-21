-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcher
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredBuildLog
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedCommon
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationPhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCompile
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFullProgram
import BeaconcryptCore.Computational.RegistrationNativeMldsaOriginEvent
/-! The same Build packet and actual source stages pass through the original result projection, typed audit and concrete LowSpec dispatcher. No packet is resampled and no local source obligation remains as a caller premise. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedBuild
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

noncomputable def augmentation (handle :Nat) (payload :Option (Slice U8)) (before :RegistrationNativePlatformExtractedSdkPublic.State Private) (prior :Log) :
    RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation
      (RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential (.inl (.inr (.build handle payload))) before.1 before.2) Log :=by
  let selected:=RegistrationNativePlatformPublicAdapterConfiguredBuildLog.augmentation configuration created credential before.1.1 before.2 handle payload prior
  exact ⟨selected.sample,selected.erase⟩

noncomputable def run (handle :Nat) (payload :Option (Slice U8)) (before :RegistrationNativePlatformExtractedSdkPublic.State Private) (prior :Log) :
    ProbComp (Option PqxdhServerRegistrationPublication.Response×(RegistrationNativePlatformExtractedSdkPublic.State Private×Log)) :=
  let call:=RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential (.inl (.inr (.build handle payload))) before.1 before.2
  let augmented:=augmentation configuration created credential handle payload before prior
  (fun packet=>
    let result:=RegistrationNativePlatformPublicAdapterLoggedRuntime.answer call (RegistrationNativePlatformPublicAdapterLoggedRuntime.project call augmented packet)
    (result.1,(result.2,packet.val.2))) <$>PFunctor.FreeM.attachSupp augmented.sample

theorem source_joint (handle :Nat) (payload :Option (Slice U8)) (before :RegistrationNativePlatformExtractedSdkPublic.State Private) (prior :Log) :
    (fun result=>RegistrationNativePlatformPublicAdapterSourceRuntime.embed
      (result.1,RegistrationNativePlatformPublicAdapterLoggedCommon.physical Private physical result.2)) <$>
      run configuration created credential handle payload before prior=
    RegistrationNativePlatformPublicAdapterBuildLoggedPhysical.operation configuration
      (RegistrationNativePlatformPublicAdapterLoggedCommon.physical Private physical (before,prior)) handle payload :=by
  have same:=RegistrationNativePlatformPublicAdapterConfiguredBuildLog.source_joint configuration created credential
    before.1.1 before.2 handle payload prior
  refine Eq.trans ?_ same
  unfold run RegistrationNativePlatformPublicAdapterConfiguredBuildLog.raw
  simp only [Functor.map_map]
  apply congrArg (fun observe=>observe <$>PFunctor.FreeM.attachSupp
    (augmentation configuration created credential handle payload before prior).sample)
  funext packet
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedBuild
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedBuild.augmentation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedBuild.augmentation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedBuild.source_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedBuild.source_joint

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcher
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedDispatch
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedCommon
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationPhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCompile
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFullProgram
import BeaconcryptCore.Computational.RegistrationNativeMldsaOriginEvent
/-! The same Finish packet and actual source stages pass through the original result projection, typed audit and concrete LowSpec dispatcher. No packet is resampled and no local source obligation remains as a caller premise. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedFinish
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

noncomputable def augmentation (index :Nat) (input :Slice U8) (before :RegistrationNativePlatformExtractedSdkPublic.State Private) (prior :Log) :
    RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation
      (RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential (.inl (.inr (.finish index input))) before.1 before.2) Log :=by
  let selected:=RegistrationNativePlatformPublicAdapterFinishLoggedDispatch.stepAugmentation configuration created credential
    before.1.1 before.2 index input RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior
  exact ⟨selected.sample,selected.erase⟩

noncomputable def run (index :Nat) (input :Slice U8) (before :RegistrationNativePlatformExtractedSdkPublic.State Private) (prior :Log) :
    ProbComp (Option Pqxdh.Bytes×(RegistrationNativePlatformExtractedSdkPublic.State Private×Log)) :=
  let call:=RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential (.inl (.inr (.finish index input))) before.1 before.2
  let augmented:=augmentation configuration created credential index input before prior
  (fun packet=>
    let result:=RegistrationNativePlatformPublicAdapterLoggedRuntime.answer call (RegistrationNativePlatformPublicAdapterLoggedRuntime.project call augmented packet)
    (result.1,(result.2,packet.val.2))) <$>PFunctor.FreeM.attachSupp augmented.sample

theorem source_joint (index :Nat) (input :Slice U8) (before :RegistrationNativePlatformExtractedSdkPublic.State Private) (prior :Log) :
    (fun result=>RegistrationNativePlatformPublicAdapterSourceRuntime.embed
      (result.1,RegistrationNativePlatformPublicAdapterLoggedCommon.physical Private physical result.2)) <$>
      run configuration created credential index input before prior=
    RegistrationNativePlatformPublicAdapterFinishLoggedPhysical.operation configuration created
      (RegistrationNativePlatformPublicAdapterLoggedCommon.physical Private physical (before,prior)) index input :=by
  have same:=congrArg (fun action=>(Prod.map (Functor.map (Prod.map id RegistrationNativePlatformPublicAdapterSourceRuntime.objects)) id) <$>action)
    (RegistrationNativePlatformPublicAdapterFinishLoggedDispatch.step_query configuration created credential
      before.1.1 before.2 index input RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior)
  change _=RegistrationNativePlatformPublicAdapterFinishLoggedPhysical.operation configuration created
    (RegistrationNativePlatformPublicAdapterLoggedCommon.physical Private physical (before,prior)) index input at same
  refine Eq.trans ?_ same
  unfold run RegistrationNativePlatformPublicAdapterFinishLoggedDispatch.publicOutput
  simp only [Functor.map_map]
  apply congrArg (fun observe=>observe <$>PFunctor.FreeM.attachSupp
    (augmentation configuration created credential index input before prior).sample)
  funext packet
  dsimp only [augmentation,RegistrationNativePlatformPublicAdapterDispatcher.calls,
    RegistrationNativePlatformPublicAdapterDispatcher.publicCalls,RegistrationNativePlatformPublicAdapterAuditedFinish.step,
    RegistrationNativePlatformPublicAdapterAuditedFinish.typed,RegistrationNativePlatformPublicAdapterAuditLift.selected,
    RegistrationNativePlatformPublicAdapterConfiguredFinish.step,RegistrationNativePlatformPublicAdapterBuildRaw.modelCast,
    RegistrationNativePlatformPublicAdapterReply.map,RegistrationNativePlatformPublicAdapterTypedAudit.lift,
    RegistrationNativePlatformPublicAdapterFinishLoggedDispatch.stepAugmentation,
    RegistrationNativePlatformPublicAdapterLoggedRuntime.answer,RegistrationNativePlatformPublicAdapterLoggedRuntime.project,
    RegistrationNativePlatformPublicAdapterSourceRuntime.embed,RegistrationNativePlatformPublicAdapterLoggedCommon.physical,
    RegistrationNativePlatformPublicAdapterFinishLoggedJoint.physicalLog,RegistrationNativePlatformPublicAdapterAuditLowModel.physical,
    RegistrationNativePlatformPublicAdapterAuditModel.physical]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedFinish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedFinish.augmentation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedFinish.augmentation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedFinish.source_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedFinish.source_joint

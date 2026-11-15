-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishLoggedHistory
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSigningAligned
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
local notation "receipts"=>RegistrationNativePlatformPublicAdapterSourceSigningHistory.receipts
local notation "stages"=>RegistrationNativePlatformPublicAdapterSourceAuthentication.stages

theorem suffix (index :Nat) (input :Slice U8) (before :RegistrationNativePlatformExtractedSdkPublic.State Private) (prior :Log)
    (result :(RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential (.inl (.inr (.finish index input))) before.1 before.2).step.Packet×Log)
    (supported :result∈support (RegistrationNativePlatformPublicAdapterLoggedFinish.augmentation configuration created credential index input before prior).sample) :
    ∃middle :List Stage,result.2=prior++middle.map RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage :=by
  exact RegistrationNativePlatformPublicAdapterFinishLoggedHistory.suffix configuration created credential before.1.1 before.2 index input prior result supported

theorem aligned (index :Nat) (input :Slice U8) (before :RegistrationNativePlatformExtractedSdkPublic.State Private) (prior :Log)
    (held :before.1.1.1.server.world.world.2=receipts (stages prior))
    (result :(RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential (.inl (.inr (.finish index input))) before.1 before.2).step.Packet×Log)
    (supported :result∈support (RegistrationNativePlatformPublicAdapterLoggedFinish.augmentation configuration created credential index input before prior).sample) :
    ((RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential (.inl (.inr (.finish index input))) before.1 before.2).step.native result.1).2.1.1.server.world.world.2=
      receipts (stages result.2) :=by
  let call:=RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential (.inl (.inr (.finish index input))) before.1 before.2
  let augmented:=RegistrationNativePlatformPublicAdapterLoggedFinish.augmentation configuration created credential index input before prior
  have called:result.1∈support call.step.sample :=by
    rw [←augmented.erase,support_map]
    exact ⟨result,supported,rfl⟩
  have native:call.step.native result.1∈support ((RegistrationNativePlatformPublicAdapterAuditLowModel.model configuration created credential (.inl (.inr (.finish index input)))).run before.1) :=by
    have mapped:call.step.native result.1∈support (call.step.native <$>call.step.sample) :=by
      rw [support_map]
      exact ⟨result.1,called,rfl⟩
    exact Eq.mp (congrArg (fun action=>call.step.native result.1∈support action) call.step.native_exact) mapped
  have publicSupport:=Eq.mp (congrArg (fun action=>call.step.native result.1∈support (action.run before.1))
    (RegistrationNativePlatformPublicAdapterAuditLowModel.public_query configuration created credential (.inr (.finish index input)))) native
  have frame:=RegistrationNativePlatformPublicAdapterSigningQuiet.raw configuration created credential
    (.inr (.finish index (TranscriptAuthParts.absSlice input))) (by trivial) before.1 (call.step.native result.1) publicSupport
  have source:=RegistrationNativePlatformPublicAdapterFinishLoggedHistory.configured configuration created credential before.1.1 before.2 index input
    RegistrationNativePlatformPublicAdapterSourceEvents.Event.stage prior result supported
  rcases source with same|⟨initial,reply,same⟩
  · rw [same]
    exact frame.trans held
  · rw [same]
    simpa only [RegistrationNativePlatformPublicAdapterSourceAuthentication.stages,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
      RegistrationNativePlatformPublicAdapterSourceSigningHistory.receipts,RegistrationNativePlatformPublicAdapterSourceSigningHistory.receipt,List.append_nil] using frame.trans held

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSigningAligned

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSigningAligned.suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSigningAligned.suffix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSigningAligned.aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFinishSigningAligned.aligned

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSigningHistory
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationLoop
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
open RegistrationNativePlatformPublicAdapterSourceEvents (Event)
local notation "receipts"=>RegistrationNativePlatformPublicAdapterSourceSigningHistory.receipts
local notation "stages"=>RegistrationNativePlatformPublicAdapterSourceAuthentication.stages
local notation "flag"=>RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.flag configuration.view credential.publicKey
local notation "model"=>RegistrationNativePlatformPublicAdapterAuditLowModel.model configuration created credential
local notation "State"=>RegistrationNativePlatformPublicAdapterLoggedJoint.State (n:=n) configuration created credential

abbrev Invariant (before :State) :Prop :=RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback.Invariant configuration created credential before

local notation "calls"=>RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential
local notation "augmentation"=>RegistrationNativePlatformPublicAdapterLoggedJoint.augmentation configuration created credential
local notation "Low"=>RegistrationNativePlatformPublicAdapterLowSpec.Spec

theorem query (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain) (before :State) (held :Invariant configuration created credential before)
    (result :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Range query×State)
    (supported :result∈support ((RegistrationNativePlatformPublicAdapterLoggedJoint.handler configuration created credential query).run before)) :
    Invariant configuration created credential result.2 :=by
  obtain ⟨packet,output⟩:=RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback.query_cut configuration created credential query before result supported
  let openedPrior:=before.2++[Event.opened query (physical before.1.1 before.1.2)]
  let call:=calls query before.1.1 before.1.2
  let augmented:=augmentation query before.1 openedPrior
  let chosen:=RegistrationNativePlatformPublicAdapterLoggedRuntime.project call augmented packet
  let answer:=RegistrationNativePlatformPublicAdapterLoggedRuntime.answer call chosen
  change result=(answer.1,(answer.2,packet.val.2++[Event.closed query
    (.ok (answer.1,RegistrationNativePlatformPublicAdapterSourceRuntime.objects (physical answer.2.1 answer.2.2)))
    (physical answer.2.1 answer.2.2).backend])) at output
  obtain ⟨middle,logEq⟩:=RegistrationNativePlatformPublicAdapterSigningHistory.suffix configuration created credential query before.1 openedPrior packet.val packet.property
  have initialHistory:before.1.1.1.1.server.world.world.2=receipts (stages openedPrior):=by
    simpa only [openedPrior,RegistrationNativePlatformPublicAdapterSourceAuthentication.stages,List.filterMap_append,
      List.filterMap_cons,List.filterMap_nil,List.append_nil] using held.1
  have finalHistory:=RegistrationNativePlatformPublicAdapterSigningHistory.aligned configuration created credential query before.1 openedPrior initialHistory packet.val packet.property
  have nativeSupport:=RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback.packet_native configuration created credential query before.1 openedPrior packet
  have publicReply:answer.1=(call.step.native packet.val.1).1:=
    call.reply chosen.val chosen.property (RegistrationNativePlatformExtractedSdkPublic.returned call chosen)
      (RegistrationNativePlatformExtractedSdkPublic.returned_exact call chosen)
  have actualSupport:(answer.1,answer.2.1)∈support ((model query).run before.1.1):=by
    rw [publicReply]
    exact nativeSupport
  have history:answer.2.1.1.1.server.world.world.2=receipts (stages before.2++middle):=by
    change (call.step.native packet.val.1).2.1.1.server.world.world.2=receipts (stages before.2++middle)
    rw [logEq] at finalHistory
    simpa only [openedPrior,RegistrationNativePlatformPublicAdapterSourceAuthentication.stages,List.filterMap_append,
      List.filterMap_cons,List.filterMap_nil,List.filterMap_map,List.filterMap_some,Function.comp_def,List.append_nil] using finalHistory
  have preserved:=RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback.boundary configuration created credential
    query before.1 answer.2 before.2 middle answer.1 held actualSupport history
  rw [output]
  change Invariant configuration created credential (answer.2,packet.val.2++[Event.closed query
    (.ok (answer.1,RegistrationNativePlatformPublicAdapterSourceRuntime.objects (physical answer.2.1 answer.2.2)))
    (physical answer.2.1 answer.2.2).backend])
  rw [logEq]
  simpa only [openedPrior,List.append_assoc] using preserved

theorem program (work :OracleComp Low Value) (before :State) (held :Invariant configuration created credential before)
    (result :Value×State)
    (supported :result∈support ((simulateQ (RegistrationNativePlatformPublicAdapterLoggedJoint.handler configuration created credential) work).run before)) :
    Invariant configuration created credential result.2 :=
  PqxdhRecordLiftFlat.support_keep_oracle (RegistrationNativePlatformPublicAdapterLoggedJoint.handler configuration created credential)
    (Invariant configuration created credential) (query configuration created credential) work before held result supported

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationLoop

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationLoop.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationLoop.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationLoop.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationLoop.program

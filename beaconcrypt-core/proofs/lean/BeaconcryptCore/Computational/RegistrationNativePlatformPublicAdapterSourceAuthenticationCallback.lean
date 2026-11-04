-- SPDX-License-Identifier: 0BSD
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback
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

noncomputable def Invariant (before :State) :Prop :=
  before.1.1.1.1.server.world.world.2=receipts (stages before.2) ∧(flag before.2=true→before.1.1.2.bad=true)

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
theorem callback_flag (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain)
    (before :RegistrationNativePlatformPublicAdapterStore.Store n KemSK R P) (prior :Log) (middle :List Stage)
    (reply :RustM (RegistrationNativePlatformPublicAdapterLowSpec.Spec.Range query×RegistrationNativePlatformPublicAdapterSourceRuntime.Objects R))
    (after :RegistrationNativePlatformSdkReification.Backend n KemSK×P) :
    flag (prior++([Event.opened query before]++middle.map Event.stage++[Event.closed query reply after]))=
      (flag prior ||RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.closed configuration.view credential.publicKey
        (some (before,stages prior)) query reply after) :=by
  unfold RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.flag
  rw [RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.run_append,
    RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.callback_bad,
    RegistrationNativePlatformPublicAdapterSourceAuthenticationMonitor.history_run]
  rfl

omit [PublicWrapperPlatform.CryptoOperations] in
theorem boundary (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain)
    (before after :RegistrationNativePlatformExtractedSdkPublic.State Private) (prior :Log) (middle :List Stage)
    (reply :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Range query)
    (held :Invariant configuration created credential (before,prior))
    (supported :(reply,after.1)∈support ((model query).run before.1))
    (history :after.1.1.1.server.world.world.2=receipts (stages prior++middle)) :
    Invariant configuration created credential (after,prior++([Event.opened query (physical before.1 before.2)]++middle.map Event.stage++
      [Event.closed query (.ok (reply,RegistrationNativePlatformPublicAdapterSourceRuntime.objects (physical after.1 after.2))) (physical after.1 after.2).backend])) :=by
  constructor
  · simpa only [RegistrationNativePlatformPublicAdapterSourceAuthentication.stages,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
      List.filterMap_map,List.filterMap_some,List.append_nil,List.nil_append,Function.comp_def] using history
  · intro marked
    rw [callback_flag] at marked
    rcases Bool.or_eq_true_iff.mp marked with old|new
    · exact RegistrationNativePlatformPublicAdapterSourceAuthenticationAudit.monotone configuration created credential query before.1 (reply,after.1) supported (held.2 old)
    · exact RegistrationNativePlatformPublicAdapterSourceAuthenticationAudit.closed_bad configuration created credential query before after (stages prior) held.1 reply supported new

/- The callback boundary exposes the given supported augmented packet; it is not a new compatible execution. -/
theorem query_cut (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain) (before :State)
    (result :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Range query×State)
    (supported :result∈support ((RegistrationNativePlatformPublicAdapterLoggedJoint.handler configuration created credential query).run before)) :
    ∃packet :{value //value∈support (RegistrationNativePlatformPublicAdapterLoggedJoint.augmentation configuration created credential query before.1
      (before.2++[Event.opened query (physical before.1.1 before.1.2)])).sample},
      let call:=RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential query before.1.1 before.1.2
      let augmented:=RegistrationNativePlatformPublicAdapterLoggedJoint.augmentation configuration created credential query before.1
        (before.2++[Event.opened query (physical before.1.1 before.1.2)])
      let answered:=RegistrationNativePlatformPublicAdapterLoggedRuntime.answer call (RegistrationNativePlatformPublicAdapterLoggedRuntime.project call augmented packet)
      result=(answered.1,(answered.2,packet.val.2++[Event.closed query
        (.ok (answered.1,RegistrationNativePlatformPublicAdapterSourceRuntime.objects (physical answered.2.1 answered.2.2)))
        (physical answered.2.1 answered.2.2).backend])) :=by
  change result∈support (RegistrationNativePlatformPublicAdapterLoggedCommon.closed Private physical query <$>
    (RegistrationNativePlatformPublicAdapterLoggedRuntime.handler Private model (RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential)
      (RegistrationNativePlatformPublicAdapterLoggedJoint.augmentation configuration created credential) query).run
      (RegistrationNativePlatformPublicAdapterLoggedCommon.opened Private physical query before)) at supported
  rw [support_map] at supported
  obtain ⟨middle,reached,equal⟩:=supported
  simp only [RegistrationNativePlatformPublicAdapterLoggedRuntime.handler,StateT.run,support_map] at reached
  obtain ⟨packet,_attached,same⟩:=reached
  exact ⟨packet,by rw [←equal,←same];rfl⟩

theorem packet_native (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain)
    (before :RegistrationNativePlatformExtractedSdkPublic.State Private) (prior :Log)
    (packet :{value //value∈support (RegistrationNativePlatformPublicAdapterLoggedJoint.augmentation configuration created credential query before prior).sample}) :
    let call:=RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential query before.1 before.2
    call.step.native packet.val.1∈support ((model query).run before.1) :=by
  let call:=RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential query before.1 before.2
  let augmented:=RegistrationNativePlatformPublicAdapterLoggedJoint.augmentation configuration created credential query before prior
  have original:packet.val.1∈support call.step.sample:=
    (RegistrationNativePlatformPublicAdapterLoggedRuntime.project call augmented packet).property
  have mapped:call.step.native packet.val.1∈support (call.step.native <$>call.step.sample):=by
    rw [support_map]
    exact ⟨packet.val.1,original,rfl⟩
  exact Eq.mp (congrArg (fun computation=>call.step.native packet.val.1∈support computation) call.step.native_exact) mapped

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback.callback_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback.callback_flag

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback.boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback.boundary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback.query_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback.query_cut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback.packet_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAuthenticationCallback.packet_native

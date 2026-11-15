-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterDispatcher
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedBundle
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedBuild
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedDispatcher
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedNoStage
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedCommon
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationPhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCompile
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFullProgram
import BeaconcryptCore.Computational.RegistrationNativeMldsaOriginEvent
/-! The initialized public dispatcher carries the same sampled source packet, actual persistent backend, typed audit and callback observations. Bundle, Build and Finish expose actual stages; every other callback preserves the stage history. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedJoint
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

local notation "model"=>RegistrationNativePlatformPublicAdapterAuditLowModel.model (n:=n) configuration created credential
local notation "calls"=>RegistrationNativePlatformPublicAdapterDispatcher.calls (n:=n) configuration created credential

abbrev State :=RegistrationNativePlatformPublicAdapterLoggedCommon.State Private n KemSK R P

noncomputable def augmentation (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain)
    (before :RegistrationNativePlatformExtractedSdkPublic.State Private) (prior :Log) :
    RegistrationNativePlatformPublicAdapterLoggedRuntime.Augmentation (calls query before.1 before.2) Log :=
  match query with
  | .inl (.inr (.bundle index))=>RegistrationNativePlatformPublicAdapterLoggedBundle.augmentation configuration created credential index before prior
  | .inl (.inr (.build handle payload))=>RegistrationNativePlatformPublicAdapterLoggedBuild.augmentation configuration created credential handle payload before prior
  | .inl (.inr (.finish index input))=>RegistrationNativePlatformPublicAdapterLoggedFinish.augmentation configuration created credential index input before prior
  | query=>RegistrationNativePlatformPublicAdapterLoggedRuntime.unchanged (calls query before.1 before.2) prior

noncomputable def handler :QueryImpl RegistrationNativePlatformPublicAdapterLowSpec.Spec
    (StateT (State (n:=n) configuration created credential) ProbComp) :=
  RegistrationNativePlatformPublicAdapterLoggedCommon.handler Private model calls physical (augmentation configuration created credential)

noncomputable def sourceState (before :State (n:=n) configuration created credential) :RegistrationNativePlatformPublicAdapterSourceEvents.State n KemSK R P :=
  RegistrationNativePlatformPublicAdapterLoggedCommon.physical Private physical before

theorem program_erase (work :OracleComp RegistrationNativePlatformPublicAdapterLowSpec.Spec Value)
    (before :State (n:=n) configuration created credential) :
    Prod.map id Prod.fst <$>(simulateQ (handler configuration created credential) work).run before=
      (simulateQ (RegistrationNativePlatformExtractedSdkPublic.handler Private model calls) work).run before.1 :=
  RegistrationNativePlatformPublicAdapterLoggedCommon.program_erase Private model calls physical
    (augmentation configuration created credential) work before

theorem stage_joint (query :RegistrationNativePlatformPublicAdapterLowSpec.Spec.Domain)
    (before :State (n:=n) configuration created credential) :
    (fun result=>RegistrationNativePlatformPublicAdapterSourceRuntime.embed
      (result.1,sourceState configuration created credential result.2)) <$>
      (RegistrationNativePlatformPublicAdapterLoggedRuntime.handler Private model calls (augmentation configuration created credential) query).run before=
    RegistrationNativePlatformPublicAdapterSourceRuntime.run
      (RegistrationNativePlatformPublicAdapterLoggedDispatcher.stages configuration created query)
      (sourceState configuration created credential before) :=by
  cases query with
  | inr refused=>
    exact RegistrationNativePlatformPublicAdapterLoggedNoStage.joint Private model calls physical (.inr refused)
      (RegistrationNativePlatformPublicAdapterDispatcher.interpreter configuration created (.inr refused))
      (RegistrationNativePlatformPublicAdapterDispatcher.query configuration created credential (.inr refused)) before
  | inl publicQuery=>cases publicQuery with
    | inl coins=>
      exact RegistrationNativePlatformPublicAdapterLoggedNoStage.joint Private model calls physical (.inl (.inl coins))
        (RegistrationNativePlatformPublicAdapterDispatcher.interpreter configuration created (.inl (.inl coins)))
        (RegistrationNativePlatformPublicAdapterDispatcher.query configuration created credential (.inl (.inl coins))) before
    | inr command=>cases command with
      | bundle index=>
        change (fun result=>RegistrationNativePlatformPublicAdapterSourceRuntime.embed
          (result.1,sourceState configuration created credential result.2)) <$>
          RegistrationNativePlatformPublicAdapterLoggedBundle.run configuration created credential index before.1 before.2=_
        rw [RegistrationNativePlatformPublicAdapterLoggedDispatcher.stages,RegistrationNativePlatformPublicAdapterSourceLogLift.run_outcome]
        exact RegistrationNativePlatformPublicAdapterLoggedBundle.source_joint configuration created credential index before.1 before.2
      | build handle payload=>
        change (fun result=>RegistrationNativePlatformPublicAdapterSourceRuntime.embed
          (result.1,sourceState configuration created credential result.2)) <$>
          RegistrationNativePlatformPublicAdapterLoggedBuild.run configuration created credential handle payload before.1 before.2=_
        rw [RegistrationNativePlatformPublicAdapterLoggedDispatcher.stages,RegistrationNativePlatformPublicAdapterSourceLogLift.run_outcome]
        exact (RegistrationNativePlatformPublicAdapterLoggedBuild.source_joint configuration created credential handle payload before.1 before.2).trans
          (RegistrationNativePlatformPublicAdapterBuildLoggedActualSource.operation_source configuration
            (sourceState configuration created credential before) handle payload)
      | finish index input=>
        change (fun result=>RegistrationNativePlatformPublicAdapterSourceRuntime.embed
          (result.1,sourceState configuration created credential result.2)) <$>
          RegistrationNativePlatformPublicAdapterLoggedFinish.run configuration created credential index input before.1 before.2=_
        rw [RegistrationNativePlatformPublicAdapterLoggedDispatcher.stages,RegistrationNativePlatformPublicAdapterSourceLogLift.run_outcome]
        exact RegistrationNativePlatformPublicAdapterLoggedFinish.source_joint configuration created credential index input before.1 before.2
      | _=>
        exact RegistrationNativePlatformPublicAdapterLoggedNoStage.joint Private model calls physical _ _
          (RegistrationNativePlatformPublicAdapterDispatcher.query configuration created credential _) before

theorem program_source (work :OracleComp RegistrationNativePlatformPublicAdapterLowSpec.Spec Value)
    (before :State (n:=n) configuration created credential) :
    (fun result=>RegistrationNativePlatformPublicAdapterSourceRuntime.embed
      (result.1,sourceState configuration created credential result.2)) <$>
      (simulateQ (handler configuration created credential) work).run before=
    RegistrationNativePlatformPublicAdapterSourceRuntime.run
      (simulateQ (RegistrationNativePlatformPublicAdapterLoggedDispatcher.interpreter configuration created) work)
      (sourceState configuration created credential before) :=
  RegistrationNativePlatformPublicAdapterLoggedCommon.program_source Private model calls physical
    (augmentation configuration created credential) (RegistrationNativePlatformPublicAdapterLoggedDispatcher.stages configuration created)
    (stage_joint configuration created credential) work before

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedJoint
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedJoint.augmentation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedJoint.augmentation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedJoint.program_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedJoint.program_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedJoint.stage_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedJoint.stage_joint
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedJoint.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedJoint.program_source

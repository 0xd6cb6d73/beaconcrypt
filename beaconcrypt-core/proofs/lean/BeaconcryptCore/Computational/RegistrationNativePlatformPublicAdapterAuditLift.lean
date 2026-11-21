-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditModel
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBuildModel
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInterface
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterEffectPhysical
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLift
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
variable {n :Nat} {I KemSK P E R Error S A :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
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
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "coins"=>RegistrationNativePlatformMldsaProgram.coins
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
local notation "N"=>RegistrationNativeExperiment.State n KemSK source×P
local notation "Audit"=>RegistrationNativePlatformPublicAdapterTypedAudit.Audit RegistrationNativeRawAdapter.TypedSpec N
variable (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential :RegistrationNativeMldsa.Credential source)
local notation "objects"=>RegistrationNativePlatformPublicAdapterDispatcherCore.Private configuration created credential
local notation "typed"=>RegistrationNativePlatformPublicAdapterAuditModel.typed configuration created credential
local notation "failure"=>RegistrationNativePlatformPublicAdapterAuditModel.failure credential
local notation "publicPhysical"=>RegistrationNativePlatformPublicAdapterDispatcherCore.physical configuration created credential
local notation "auditPhysical"=>RegistrationNativePlatformPublicAdapterAuditModel.physical configuration created credential

omit [PublicWrapperPlatform.CryptoOperations] in
theorem selected_target (query :RegistrationNativeInterface.Spec.Domain) (chosen :RegistrationNativeRawAdapter.TypedSpec.Domain)
    (observe :RegistrationNativeRawAdapter.TypedSpec.Range chosen→RegistrationNativeInterface.Spec.Range query)
    (shape :RegistrationNativePlatformPublicAdapterTypedAuditRaw.form RegistrationNativeConcreteCodec.wire query=.query chosen observe)
    (current :N) (prior :Audit) :
    Prod.map observe id <$>(RegistrationNativePlatformPublicAdapterTypedAudit.handler typed failure chosen).run (current,prior)=
      (RegistrationNativePlatformPublicAdapterAuditModel.raw configuration created credential query).run (current,prior) :=by
  have actual:=RegistrationNativePlatformPublicAdapterTypedAuditRaw.query RegistrationNativeConcreteCodec.wire typed failure query (current,prior)
  rw [shape] at actual
  exact actual.symm

noncomputable def selected (query :RegistrationNativeInterface.Spec.Domain) (chosen :RegistrationNativeRawAdapter.TypedSpec.Domain)
    (observe :RegistrationNativeRawAdapter.TypedSpec.Range chosen→RegistrationNativeInterface.Spec.Range query)
    (shape :RegistrationNativePlatformPublicAdapterTypedAuditRaw.form RegistrationNativeConcreteCodec.wire query=.query chosen observe)
    (current :N) (prior :Audit) (call :TotalStep objects ((typed chosen).run current)) :
    TotalStep (RegistrationNativePlatformPublicAdapterAuditModel.Private configuration created credential)
      ((RegistrationNativePlatformPublicAdapterAuditModel.raw configuration created credential query).run (current,prior)) :=
  RegistrationNativePlatformPublicAdapterBuildRaw.modelCast
    (selected_target configuration created credential query chosen observe shape current prior)
    (RegistrationNativePlatformPublicAdapterReply.map observe
      (RegistrationNativePlatformPublicAdapterTypedAudit.lift typed failure objects chosen current prior call))

omit [PublicWrapperPlatform.CryptoOperations] in
theorem selected_physical (query :RegistrationNativeInterface.Spec.Domain) (chosen :RegistrationNativeRawAdapter.TypedSpec.Domain)
    (observe :RegistrationNativeRawAdapter.TypedSpec.Range chosen→RegistrationNativeInterface.Spec.Range query)
    (shape :RegistrationNativePlatformPublicAdapterTypedAuditRaw.form RegistrationNativeConcreteCodec.wire query=.query chosen observe)
    (current :N) (prior :Audit) (call :TotalStep objects ((typed chosen).run current)) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw auditPhysical
      (selected configuration created credential query chosen observe shape current prior call)=
      RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw publicPhysical
        (RegistrationNativePlatformPublicAdapterReply.map observe call) :=by
  unfold selected
  rw [RegistrationNativePlatformPublicAdapterDispatcherCore.raw_cast]
  exact RegistrationNativePlatformPublicAdapterTypedAudit.physical typed failure objects chosen current prior call observe publicPhysical

omit [PublicWrapperPlatform.CryptoOperations] in
theorem silent_target (query :RegistrationNativeInterface.Spec.Domain) (value :RegistrationNativeInterface.Spec.Range query)
    (shape :RegistrationNativePlatformPublicAdapterTypedAuditRaw.form RegistrationNativeConcreteCodec.wire query=.pure value)
    (current :N) (prior :Audit) :
    (fun result=>(result.1,(result.2,prior))) <$>
      (RegistrationNativePlatformPackedState.pack
        (RegistrationNativePlatformPublicAdapterDispatcherCore.native configuration created credential query)).run current=
      (RegistrationNativePlatformPublicAdapterAuditModel.raw configuration created credential query).run (current,prior) :=by
  have actual:=RegistrationNativePlatformPublicAdapterTypedAuditRaw.query RegistrationNativeConcreteCodec.wire typed failure query (current,prior)
  rw [shape] at actual
  have mapped:=congrArg (fun tree=>Prod.map id Prod.fst <$>tree) actual
  have base:=(RegistrationNativePlatformPublicAdapterAuditModel.raw_native configuration created credential query (current,prior)).symm.trans mapped
  simp only [map_pure,Prod.map,id_eq] at base
  rw [base,map_pure]
  exact actual.symm

noncomputable def silenced (query :RegistrationNativeInterface.Spec.Domain) (value :RegistrationNativeInterface.Spec.Range query)
    (shape :RegistrationNativePlatformPublicAdapterTypedAuditRaw.form RegistrationNativeConcreteCodec.wire query=.pure value)
    (current :N) (prior :Audit)
    (call :TotalStep objects ((RegistrationNativePlatformPackedState.pack
      (RegistrationNativePlatformPublicAdapterDispatcherCore.native configuration created credential query)).run current)) :
    TotalStep (RegistrationNativePlatformPublicAdapterAuditModel.Private configuration created credential)
      ((RegistrationNativePlatformPublicAdapterAuditModel.raw configuration created credential query).run (current,prior)) :=
  RegistrationNativePlatformPublicAdapterBuildRaw.modelCast
    (silent_target configuration created credential query value shape current prior)
    (RegistrationNativePlatformPublicAdapterTypedAudit.silent objects prior call)

omit [PublicWrapperPlatform.CryptoOperations] in
theorem silenced_physical (query :RegistrationNativeInterface.Spec.Domain) (value :RegistrationNativeInterface.Spec.Range query)
    (shape :RegistrationNativePlatformPublicAdapterTypedAuditRaw.form RegistrationNativeConcreteCodec.wire query=.pure value)
    (current :N) (prior :Audit)
    (call :TotalStep objects ((RegistrationNativePlatformPackedState.pack
      (RegistrationNativePlatformPublicAdapterDispatcherCore.native configuration created credential query)).run current)) :
    RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw auditPhysical
      (silenced configuration created credential query value shape current prior call)=
      RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw publicPhysical call :=by
  unfold silenced
  rw [RegistrationNativePlatformPublicAdapterDispatcherCore.raw_cast]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLift.selected_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLift.selected_target

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLift.selected_physical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLift.selected_physical

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLift.silent_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLift.silent_target

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLift.silenced_physical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditLift.silenced_physical

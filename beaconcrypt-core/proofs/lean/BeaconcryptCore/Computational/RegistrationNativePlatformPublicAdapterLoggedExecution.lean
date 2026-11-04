-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedJoint
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterExecution
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationPhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCompile
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFullProgram
import BeaconcryptCore.Computational.RegistrationNativeMldsaOriginEvent
/-! Initialized execution uses actual returned source objects, RNG and sampled physical World. Its event transport consumes the internally discharged concrete dispatcher source law, retaining returned values, the full secrecy ledger and persistent platform state. Its common source projection retains the chronological operation log; its native projection retains the original complete ledger and physical state. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedExecution
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
variable [AdapterServerConstructorPrimitive.Standard]
variable {Value :Type}
variable (objects :AdapterServerConstructorObjects.Leaves configuration.views)
variable (ensureInit :StateT Unit ProbComp Bool)
variable (serverEd :AdapterServerConstructorJoint.EdContract configuration.generator configuration.view setup.joint (AdapterServerConstructorStartup.edCore ensureInit))
variable (identityIndex :Nat) (identifier :U64) (rng :R)
variable (bounds :PqxdhDeploymentInterface.FreshBounds) (mode :PqxdhDeploymentInterface.Mode)
variable (adversary :RegistrationNativeExperiment.Public→OracleComp (RegistrationNativePlatformPublicAdapterInterface.ModeSpec mode) Value)
variable (decision :RegistrationNativeExperiment.Public→(Value×RegistrationNativeLedger.State)→
  RegistrationNativePlatformPublicAdapterSourceEvents.State n KemSK R P→Bool)
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "AuditState"=>RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source
local notation "wire"=>RegistrationNativeConcreteCodec.wire
local notation "canonical"=>RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "codec"=>RegistrationNativeWire.ledgerCodec canonical

noncomputable def commonProfile :StateT P ProbComp Bool :=fun previous=>do
  let packet←RegistrationNativePlatformPublicAdapterInitializationPhysical.sample (n:=n) setup configuration.generator configuration.view previous identityIndex identifier rng
  match returned:packet.val.1.ready with
  | none=>pure (false,previous)
  | some ready=>
    let stored:=RegistrationNativePlatformPublicAdapterInitializationPhysical.carrier setup configuration.generator configuration.view configuration.views objects ensureInit
      serverEd configuration.mlGeneration configuration.edGetter configuration.mlGetter previous identityIndex identifier rng packet ready returned
    (fun result=>RegistrationNativePlatformPublicAdapterExecution.observe decision ready.initial.public
      (RegistrationNativePlatformPublicAdapterSourceRuntime.embed
        (result.1,RegistrationNativePlatformPublicAdapterLoggedJoint.sourceState configuration ready.initial.created ready.initial.credential result.2))) <$>
      (simulateQ (RegistrationNativePlatformPublicAdapterLoggedJoint.handler configuration ready.initial.created ready.initial.credential)
        (RegistrationNativePlatformPublicAdapterLedgerExecution.work (setup:=setup) bounds mode adversary ready.initial.public)).run
        (⟨((ready.initial.state,previous),RegistrationNativePlatformPublicAdapterTypedAudit.empty),stored⟩,[])

include objects serverEd in
theorem common_source :
    commonProfile (n:=n) configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary decision=
      RegistrationNativePlatformPublicAdapterExecution.profile (n:=n) configuration identityIndex identifier rng bounds mode adversary decision :=by
  funext previous
  unfold commonProfile RegistrationNativePlatformPublicAdapterExecution.profile
  apply bind_congr
  rintro ⟨⟨⟨constructor,choice⟩,world⟩,supported⟩
  cases choice with
  | none=>rfl
  | some ready=>
    dsimp only
    let packet :{value //value∈support (RegistrationNativePlatformPublicAdapterInitializationPhysical.raw (n:=n) setup configuration.generator configuration.view previous identityIndex identifier rng)}:=⟨(⟨constructor,some ready⟩,world),supported⟩
    let stored:=RegistrationNativePlatformPublicAdapterInitializationPhysical.carrier setup configuration.generator configuration.view configuration.views objects ensureInit serverEd
      configuration.mlGeneration configuration.edGetter configuration.mlGetter previous identityIndex identifier rng packet ready rfl
    let start :RegistrationNativePlatformPublicAdapterLoggedJoint.State (n:=n) configuration ready.initial.created ready.initial.credential:=
      (⟨((ready.initial.state,previous),RegistrationNativePlatformPublicAdapterTypedAudit.empty),stored⟩,[])
    have initialized:=RegistrationNativePlatformPublicAdapterInitializationPhysical.physical setup configuration.generator configuration.view configuration.views objects ensureInit serverEd
      configuration.mlGeneration configuration.edGetter configuration.mlGetter previous identityIndex identifier rng packet ready rfl
    change RegistrationNativePlatformPublicAdapterAuditLowModel.physical configuration ready.initial.created ready.initial.credential start.1.1 start.1.2=
      RegistrationNativePlatformPublicAdapterInitializationPhysical.initialStore world ready previous at initialized
    have initial :RegistrationNativePlatformPublicAdapterLoggedJoint.sourceState configuration ready.initial.created ready.initial.credential start=
        RegistrationNativePlatformPublicAdapterExecution.initial world ready previous :=by
      dsimp only [RegistrationNativePlatformPublicAdapterLoggedJoint.sourceState,RegistrationNativePlatformPublicAdapterLoggedCommon.physical,
        RegistrationNativePlatformPublicAdapterExecution.initial]
      rw [initialized]
    have physical:=RegistrationNativePlatformPublicAdapterLoggedJoint.program_source configuration ready.initial.created ready.initial.credential
      (RegistrationNativePlatformPublicAdapterLedgerExecution.work (setup:=setup) bounds mode adversary ready.initial.public) start
    have observed:=congrArg (fun computation=>RegistrationNativePlatformPublicAdapterExecution.observe decision ready.initial.public <$>computation) physical
    rw [Functor.map_map,initial] at observed
    exact observed

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedExecution
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedExecution.commonProfile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedExecution.commonProfile
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedExecution.common_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedExecution.common_source

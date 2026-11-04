-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKemHistoryProgram
/-! The common source sample retains its own full typed path, including each intermediate private KEM pool. A separately supported KEM lift may be compared through the public observation without identifying its erased intermediate pools. -/
open CoreModels Aeneas OracleComp OracleSpec ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceCommonPath
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
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "AuditState"=>RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source


variable (created :PqxdhLiveServerConstruction.Created Unit) (credential :RegistrationNativeMldsa.Credential source)
local notation "wire"=>RegistrationNativePlatformConcreteSource.wire
local notation "canonical"=>RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "route"=>RegistrationNativePlatformPublicAdapterRouting.route
local notation "allocation"=>RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin
local notation "helper"=>RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame
local notation "writer"=>RegistrationNativePlatformConcreteSource.writer configuration.reservePackets
local notation "typed"=>RegistrationNativePlatformPublicAdapterAuditModel.typed (n:=n) configuration created credential
local notation "failure"=>RegistrationNativePlatformPublicAdapterAuditModel.failure credential
local notation "observe"=>RegistrationNativePlatformOrdinaryKemClientJournal.observe (n:=n) (KemSK:=KemSK) (Platform:=P) (source:=source)


theorem program (serverKid :U64) (bounds :PqxdhDeploymentInterface.FreshBounds) (mode :PqxdhDeploymentInterface.Mode)
    (work :OracleComp (RegistrationNativePlatformPublicAdapterInterface.ModeSpec mode) Value)
    (current :Native×P)
    (objects :RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration created credential
      (current,RegistrationNativePlatformPublicAdapterTypedAudit.empty))
    (prior :RegistrationNativePlatformPublicAdapterSourceEvents.Log n KemSK R P)
    (result :(Value×RegistrationNativeLedger.State)×RegistrationNativePlatformPublicAdapterLoggedJoint.State (n:=n) configuration created credential)
    (supported :result∈support ((simulateQ (RegistrationNativePlatformPublicAdapterLoggedJoint.handler configuration created credential)
      (RegistrationNativePlatformPublicAdapterLedgerCompile.program setup.source.crypto (RegistrationNativeWire.ledgerCodec canonical)
        serverKid bounds mode work)).run (⟨(current,RegistrationNativePlatformPublicAdapterTypedAudit.empty),objects⟩,prior))) :
    RegistrationNativeStageTrace.Path
      (RegistrationNativePlatformOrdinaryKemClientJournal.actual setup checks wire route configuration.agreement.representation created credential
        configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased helper writer)
      current result.2.1.1.2.calls result.2.1.1.1 :=by
  let ledgerWork:=RegistrationNativePlatformPublicAdapterLedgerCompile.program setup.source.crypto (RegistrationNativeWire.ledgerCodec canonical) serverKid bounds mode work
  let start :RegistrationNativePlatformPublicAdapterLoggedJoint.State (n:=n) configuration created credential:=
    (⟨(current,RegistrationNativePlatformPublicAdapterTypedAudit.empty),objects⟩,prior)
  have native:=RegistrationNativePlatformExtractedSdkPublic.program
    (RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration created credential)
    (RegistrationNativePlatformPublicAdapterAuditLowModel.model configuration created credential)
    (RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential) ledgerWork start.1
  rw [←RegistrationNativePlatformPublicAdapterLoggedJoint.program_erase configuration created credential ledgerWork start] at native
  simp only [RegistrationNativePlatformExtractedSdkPublic.project,start,Functor.map_map] at native
  have actual :(result.1,result.2.1.1)∈support ((simulateQ
      (RegistrationNativePlatformPublicAdapterAuditLowModel.model configuration created credential) ledgerWork).run
        (current,RegistrationNativePlatformPublicAdapterTypedAudit.empty)):=by
    rw [←native,support_map]
    exact ⟨result,supported,rfl⟩
  dsimp only [ledgerWork,RegistrationNativePlatformConcreteSource.wire] at actual
  rw [RegistrationNativePlatformPublicAdapterAuditProgram.program configuration created credential serverKid bounds mode work
    (current,RegistrationNativePlatformPublicAdapterTypedAudit.empty)] at actual
  have path:=RegistrationNativePlatformPublicAdapterTypedAudit.path typed failure _ current (result.1,result.2.1.1) actual
  rw [RegistrationNativePlatformPublicAdapterKemHistoryProgram.typed_source configuration created credential] at path
  exact path

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceCommonPath
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceCommonPath.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceCommonPath.program

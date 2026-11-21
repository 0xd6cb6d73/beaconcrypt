-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedJoint
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryAgreement
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemClientJournal
/-! The same concrete source packet yields the complete live native/platform state and the chronological typed KEM observations. Only source objects, source log and audit flag are projected away; no callback is replayed, and the private live KEM pool remains present. -/
open CoreModels Aeneas OracleComp OracleSpec ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKemHistoryProgram
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


variable (created :PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential :RegistrationNativeMldsa.Credential source)
local notation "wire"=>RegistrationNativePlatformConcreteSource.wire
local notation "canonical"=>RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "route"=>RegistrationNativePlatformPublicAdapterRouting.route
local notation "allocation"=>RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin
local notation "helper"=>RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame
local notation "writer"=>RegistrationNativePlatformConcreteSource.writer configuration.reservePackets
local notation "typed"=>RegistrationNativePlatformPublicAdapterAuditModel.typed (n:=n) configuration created credential
local notation "failure"=>RegistrationNativePlatformPublicAdapterAuditModel.failure credential
local notation "observe"=>RegistrationNativePlatformOrdinaryKemClientJournal.observe (n:=n) (KemSK:=KemSK) (Platform:=P) (source:=source)

omit [PublicWrapperPlatform.CryptoOperations] in
theorem typed_source :
    typed=RegistrationNativePlatformOrdinaryKemClientJournal.actual setup checks wire route configuration.agreement.representation created credential
      configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased helper writer :=by
  exact RegistrationNativePlatformExtractedDictionaryAgreement.callback_source setup checks route configuration.agreement.representation source
    configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased
    configuration.reserveFrame configuration.reservePackets configuration.sealLength configuration.openLength configuration.converted configuration.edFunctional created credential

noncomputable def project (result :(Value×RegistrationNativeLedger.State)×RegistrationNativePlatformPublicAdapterLoggedJoint.State (n:=n) configuration created credential) :=
  (result.1,(result.2.1.1.1,result.2.1.1.2.calls.map (RegistrationNativeObservedStageTrace.mapCall observe)))

theorem program (serverKid :U64) (bounds :PqxdhDeploymentInterface.FreshBounds) (mode :PqxdhDeploymentInterface.Mode)
    (work :OracleComp (RegistrationNativePlatformPublicAdapterInterface.ModeSpec mode) Value)
    (before :RegistrationNativePlatformPublicAdapterLoggedJoint.State (n:=n) configuration created credential) :
    project configuration created credential <$>
      (simulateQ (RegistrationNativePlatformPublicAdapterLoggedJoint.handler configuration created credential)
        (RegistrationNativePlatformPublicAdapterLedgerCompile.program setup.source.crypto (RegistrationNativeWire.ledgerCodec canonical)
          serverKid bounds mode work)).run before=
      (simulateQ (RegistrationNativeObservedStageTrace.handler observe
        (RegistrationNativePlatformOrdinaryKemClientJournal.actual setup checks wire route configuration.agreement.representation created credential
          configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased helper writer))
        (RegistrationNativeFullCompiler.compile setup.source.crypto canonical serverKid bounds mode
          (RegistrationNativePlatformPublicAdapterInterface.compile mode work))).run
        (before.1.1.1,before.1.1.2.calls.map (RegistrationNativeObservedStageTrace.mapCall observe)) :=by
  let ledgerWork:=RegistrationNativePlatformPublicAdapterLedgerCompile.program setup.source.crypto (RegistrationNativeWire.ledgerCodec canonical) serverKid bounds mode work
  let nativeWork:=RegistrationNativeFullCompiler.compile setup.source.crypto canonical serverKid bounds mode
    (RegistrationNativePlatformPublicAdapterInterface.compile mode work)
  have native:=RegistrationNativePlatformExtractedSdkPublic.program
    (RegistrationNativePlatformPublicAdapterAuditLowModel.Private (n:=n) configuration created credential)
    (RegistrationNativePlatformPublicAdapterAuditLowModel.model configuration created credential)
    (RegistrationNativePlatformPublicAdapterDispatcher.calls configuration created credential) ledgerWork before.1
  rw [←RegistrationNativePlatformPublicAdapterLoggedJoint.program_erase configuration created credential ledgerWork before] at native
  simp only [RegistrationNativePlatformExtractedSdkPublic.project] at native
  have joined:=congrArg (fun computation=>Prod.map id RegistrationNativePlatformPublicAdapterTypedAudit.journal <$>computation) native
  dsimp only [ledgerWork,RegistrationNativePlatformConcreteSource.wire] at joined
  rw [RegistrationNativePlatformPublicAdapterAuditProgram.program configuration created credential serverKid bounds mode work before.1.1,
    RegistrationNativePlatformPublicAdapterTypedAudit.journal_program] at joined
  have observed:=congrArg (fun computation=>Prod.map id
    (fun current=>(current.1,current.2.map (RegistrationNativeObservedStageTrace.mapCall observe))) <$>computation) joined
  simp only [Functor.map_map] at observed
  rw [RegistrationNativeObservedStageTrace.full_project,typed_source configuration created credential] at observed
  unfold project
  simpa only [RegistrationNativePlatformConcreteSource.wire,Prod.map,id_eq,RegistrationNativePlatformExtractedSdkPublic.project,
    RegistrationNativePlatformPublicAdapterTypedAudit.journal] using observed

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKemHistoryProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKemHistoryProgram.typed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKemHistoryProgram.typed_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKemHistoryProgram.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKemHistoryProgram.program

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryAllOwnerSecurity
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLoggedExecution
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemHistorySource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterExecution
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationPhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCompile
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFullProgram
import BeaconcryptCore.Computational.RegistrationNativeMldsaOriginEvent
/-! Any event of the complete initialized native KEM observation has exactly the same probability after erasing only the finite recipient monitor and capability log. The original source-client budget derives the birth allowance internally. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKemObservationProbability
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
variable (ensureInit :StateT Unit ProbComp Bool) (identityIndex :Nat) (identifier :U64)
variable (bounds :PqxdhDeploymentInterface.FreshBounds) (mode :PqxdhDeploymentInterface.Mode)
variable (adversary :RegistrationNativeExperiment.Public→OracleComp (RegistrationNativePlatformPublicAdapterInterface.ModeSpec mode) Value)
variable (previous :P) (budget :PqxdhDeploymentInterface.Budget)
variable (bounded :∀publication,RegistrationNativePlatformPublicAdapterInterface.Respects mode budget (adversary publication))
variable (functional :PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "AuditState"=>RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source
local notation "wire"=>RegistrationNativeConcreteCodec.wire
local notation "canonical"=>RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "codec"=>RegistrationNativeWire.ledgerCodec canonical

local notation "route"=>RegistrationNativePlatformPublicAdapterRouting.route
local notation "allocation"=>RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin
local notation "helper"=>RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame
local notation "writer"=>RegistrationNativePlatformConcreteSource.writer configuration.reservePackets
local notation "compiled"=>fun publication=>RegistrationNativePlatformPublicAdapterInterface.compile mode (adversary publication)

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
include bounded in
theorem source_probability (event :((Option (RegistrationNativePlatformKemInitializedJournal.History n source Value P)×P)×PqxdhLiveKemBirth.Pool KemSK)→Prop) :
    Pr{let result ← (RegistrationNativePlatformOrdinaryKemInitializedJournal.experiment (n:=n) setup checks wire route configuration.agreement.representation
      source ensureInit identityIndex identifier configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer
      configuration.reserveFrame configuration.erased helper writer bounds mode compiled previous budget functional)}[
        event (result.2.1.1.1,result.2.1.2)]=
    Pr{let result ← (RegistrationNativePlatformOrdinaryKemHistorySource.native (n:=n) setup checks wire route configuration.agreement.representation
      source ensureInit identityIndex identifier configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer
      configuration.reserveFrame configuration.erased helper writer bounds mode compiled previous)}[event result] :=by
  let work:=(RegistrationNativePlatformOrdinaryKemInitializedJournal.program (n:=n) setup checks wire route configuration.agreement.representation
    source ensureInit identityIndex identifier configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer
    configuration.reserveFrame configuration.erased helper writer bounds mode compiled).run previous
  have births:=RegistrationNativePlatformOrdinaryKemExceptions.resource (n:=n) setup checks wire route configuration.agreement.representation
    source ensureInit identityIndex identifier configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer
    configuration.reserveFrame configuration.erased helper writer bounds mode compiled previous budget
    (fun publication=>RegistrationNativePlatformPublicAdapterInterface.compile_bound mode budget _ (bounded publication)) .birth
  simp only [RegistrationNativePlatformKemHandlerResources.allowance_birth] at births
  have birthBound :work.IsQueryBoundP RegistrationNativeKemCountedReservation.IsCreate budget.create:=by
    convert births using 1
    rfl
  have law:=(RegistrationNativeKemCountedRecipientSource.source setup functional work budget.create birthBound).prEvent_eq event
  have logged:=RegistrationNativeKemRecipientLogSource.erasure setup functional work budget.create
  rw [←logged,prEvent_map] at law
  dsimp only [work] at law
  rw [RegistrationNativePlatformOrdinaryKemHistorySource.source_history] at law
  simpa only [prEvent_map,RegistrationNativeKemRecipientLogSource.erase,RegistrationNativePlatformOrdinaryKemInitializedJournal.experiment] using law.symm

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKemObservationProbability
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKemObservationProbability.source_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKemObservationProbability.source_probability

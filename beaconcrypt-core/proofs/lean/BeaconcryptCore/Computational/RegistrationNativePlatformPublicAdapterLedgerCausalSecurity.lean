-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerExecution
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUnifiedStartupEd
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCausalEvent
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryCausal
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationPhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCompile
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFullProgram
import BeaconcryptCore.Computational.RegistrationNativeMldsaOriginEvent
/-! Historical unsigned-tuple publication is evaluated on the actual final source Beacon identity roster and original ledger, with the identical strict-before-acceptance event and original loss. The source roster relation, startup and adaptive execution correspondence are all discharged internally. -/
open CoreModels Aeneas OracleComp OracleSpec ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCausalSecurity
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
variable (identityIndex :Nat) (identifier :U64) (rng :R)
variable (bounds :PqxdhDeploymentInterface.FreshBounds) (mode :PqxdhDeploymentInterface.Mode)
variable (adversary :RegistrationNativeExperiment.Public→OracleComp (RegistrationNativePlatformPublicAdapterInterface.ModeSpec mode) Value)
local notation "wire"=>RegistrationNativePlatformConcreteSource.wire
local notation "route"=>RegistrationNativePlatformPublicAdapterRouting.route
local notation "allocation"=>RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin
local notation "helper"=>RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame
local notation "writer"=>RegistrationNativePlatformConcreteSource.writer configuration.reservePackets

noncomputable def event (result :(Value×RegistrationNativeLedger.State)×RegistrationNativePlatformPublicAdapterSourceRuntime.Objects R) :Bool:=
  RegistrationNativePlatformPublicAdapterCausalEvent.sourceCausal setup configuration.view wire result.1 result.2

include objects in
theorem profile_event :
    RegistrationNativePlatformPublicAdapterLedgerExecution.profile (n:=n) configuration identityIndex identifier rng bounds mode adversary (event configuration)=
      RegistrationNativePlatformExtractedExperiment.profile (n:=n) setup checks wire route configuration.agreement.representation source (pure true)
        identityIndex identifier configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer
        configuration.reserveFrame configuration.erased helper writer bounds mode
        (fun publication=>RegistrationNativePlatformPublicAdapterInterface.compile mode (adversary publication))
        (RegistrationNativeIdentityOriginalCausalInitialized.event (n:=n) setup wire source) :=by
  exact RegistrationNativePlatformPublicAdapterLedgerExecution.profile_source configuration objects (pure true)
    (RegistrationNativePlatformPublicAdapterUnifiedStartupEd.contract configuration) identityIndex identifier rng bounds mode adversary
    (event configuration) (RegistrationNativeIdentityOriginalCausalInitialized.event (n:=n) setup wire source)
    (by
      intro created credential current stored result
      exact RegistrationNativePlatformPublicAdapterCausalEvent.event_source setup configuration.view configuration.views created credential current.1 stored wire result.1 result.2)

include objects in
theorem causal_bound (previous :P) (budget :PqxdhDeploymentInterface.Budget)
    (bounded :∀publication,RegistrationNativePlatformPublicAdapterInterface.Respects mode budget (adversary publication))
    (shortRejects :∀(publicKey :PqxdhEd25519EufCma.Ed25519PublicKey) bytes,bytes.length<64→setup.source.crypto.verify publicKey.toList bytes=none)
    (placeholder :PqxdhEd25519EufCma.Ed25519Signature) (fallback :PqxdhJointIdentity.Forgery) :
    Pr{let result←((RegistrationNativePlatformPublicAdapterLedgerExecution.profile (n:=n) configuration identityIndex identifier rng bounds mode adversary
      (event configuration)).run previous)}[result.1=true]≤
      RegistrationNativeIdentityUnissuedInitialized.loss (n:=n) setup checks wire route configuration.agreement.representation configuration.keyView configuration.sealFailure
        allocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased helper writer source (pure true)
        identityIndex identifier bounds mode (fun publication=>RegistrationNativePlatformPublicAdapterInterface.compile mode (adversary publication)) previous budget fallback+
      RegistrationNativeIdentityCensorIssuedSecurity.loss (n:=n) setup checks route configuration.agreement.representation configuration.keyView configuration.sealFailure
        allocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased helper configuration.reservePackets source (pure true)
        identityIndex identifier bounds mode (fun publication=>RegistrationNativePlatformPublicAdapterInterface.compile mode (adversary publication)) previous budget placeholder fallback :=by
  rw [profile_event configuration objects identityIndex identifier rng bounds mode adversary]
  exact RegistrationNativePlatformExtractedDictionaryCausal.causal_bound setup checks route configuration.agreement.representation configuration.keyView configuration.sealFailure
    allocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased helper configuration.reservePackets source (pure true)
    identityIndex identifier bounds mode (fun publication=>RegistrationNativePlatformPublicAdapterInterface.compile mode (adversary publication)) previous
    configuration.sealLength configuration.openLength configuration.converted configuration.edFunctional budget
    (fun publication=>RegistrationNativePlatformPublicAdapterInterface.compile_bound mode budget _ (bounded publication)) shortRejects placeholder fallback

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCausalSecurity
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCausalSecurity.profile_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCausalSecurity.profile_event
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCausalSecurity.causal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCausalSecurity.causal_bound

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSecurity
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueSource

/-! Arbitrary public ledger events transfer to the existing selected opaque warm ideal. This is a probability comparison, independent of root-contents agreement. The complete current initialized source, actual transcript-hash effects, platform failures and public event remain unchanged; only the existing selected source/key hybrid changes. The loss is exactly the prior related-input/key-schedule, one CCA and initialized-recovery loss. -/
open CoreModels Aeneas OracleComp OracleSpec ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKeyTransfer
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
variable {I KemSK P E R Error Value :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [primitives :AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [PublicWrapperPlatform.CryptoOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] [FrameDispatchFallback.Operations]
variable [originalGenerators :AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable [originalCrypto :CryptoOperations (RustT ProbComp)]
variable [originalLocal :LocalOperations (RustT (StateT P ProbComp))]
variable [originalContainers :ContainerOperations (RustT (StateT P ProbComp))]
variable [AdapterServerConstructorPrimitive.Standard]
variable {setup :PqxdhServerAuthExperiment.Setup base KemSK} {checks :PqxdhServerAuthExperiment.Checks}
variable (configuration :RegistrationNativePlatformPublicAdapterConfiguration.Configuration
  (P:=P) (E:=E) (R:=R) (Error:=Error) (source:=source) setup checks)
variable (objects :AdapterServerConstructorObjects.Leaves configuration.views)
variable (allocation :∀before capacity,configuration.allocateJoin before capacity=configuration.reserveFrame capacity.val)

variable (identityIndex : Nat) (serverKeyId : U64) (rng : R)
variable (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
variable (adversary : RegistrationNativeExperiment.Public → OracleComp
  (RegistrationNativePlatformPublicAdapterInterface.ModeSpec mode) Value)
variable (budget : PqxdhDeploymentInterface.Budget) (previous : P)
variable (decision : Value × RegistrationNativeLedger.State → Bool)
local notation "cap" => budget.cap 4 + budget.cap 5
local notation "wire" => RegistrationNativePlatformConcreteSource.wire
local notation "route" => RegistrationNativePlatformPublicAdapterRouting.route
local notation "rawAllocation" => RegistrationNativePlatformConcreteSource.rawAllocation configuration.reserveFrame
local notation "helper" => RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame
local notation "writer" => RegistrationNativePlatformConcreteSource.writer configuration.reservePackets
local notation "compiled" => fun publication => RegistrationNativePlatformPublicAdapterInterface.compile mode (adversary publication)
local notation "observe" => fun value (_ : RegistrationNativePlatformPublicWorldObservation.RecordView) => decision value

noncomputable def actual : ProbComp Bool := Prod.fst <$>
  ((RegistrationNativePlatformPublicAdapterExecution.profile (n := cap) configuration identityIndex serverKeyId rng
    bounds mode adversary (fun _ value _ => decision value)).run previous)

/-- The target is the original accept/create pair; its generated-owner slot is the successor of the reserved Server identity slot. -/
noncomputable def ideal (target : Fin budget.accept × Fin budget.create) : ProbComp Bool :=
  RegistrationNativePlatformG3UniformOpaqueSource.hidden setup checks wire route source (pure true) identityIndex serverKeyId target.1.val configuration.keyView configuration.sealFailure rawAllocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased helper writer bounds mode compiled observe
    budget target.2.succ previous

noncomputable def loss (target : Fin budget.accept × Fin budget.create) : ℝ≥0∞ :=
  ENNReal.ofReal (RegistrationNativePlatformG3UniformOpaqueSource.initialLoss setup checks wire route source (pure true) identityIndex serverKeyId target.1.val configuration.keyView configuration.sealFailure rawAllocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased helper writer bounds mode compiled observe budget target.2.succ previous +
    RegistrationNativePlatformG3UniformOpaqueSource.kemLoss setup checks wire route source (pure true) identityIndex serverKeyId target.1.val configuration.keyView configuration.sealFailure rawAllocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased helper writer bounds mode compiled observe budget target.2.succ previous) +
  RegistrationNativePlatformG3UniformOpaque.recoveryLoss setup checks wire route source (pure true) identityIndex serverKeyId target.1.val
    configuration.keyView configuration.sealFailure rawAllocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased helper writer
    bounds mode compiled budget target.2.succ previous

include objects allocation in
/-- Equality transports the original public decision through the actual extracted runtime; it is not an event-equivalence premise. -/
theorem actual_source : actual configuration identityIndex serverKeyId rng bounds mode adversary budget previous decision =
    RegistrationNativePlatformG3UniformOpaqueSource.actual setup checks wire route source (pure true) identityIndex serverKeyId configuration.keyView configuration.sealFailure rawAllocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased helper writer bounds mode compiled observe
      configuration.agreement.representation budget previous := by
  unfold actual RegistrationNativePlatformG3UniformOpaqueSource.actual
  rw [RegistrationNativePlatformPublicAdapterSecurity.profile_event configuration objects allocation
    identityIndex serverKeyId rng bounds mode adversary decision]
  rw [RegistrationNativePlatformExtractedExperiment.profile_source setup checks wire route
    configuration.agreement.representation source (pure true) identityIndex serverKeyId
    configuration.keyView configuration.sealFailure rawAllocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased helper writer
    bounds mode compiled _ configuration.sealLength configuration.openLength configuration.converted configuration.edFunctional]

include objects allocation in
/-- The same arbitrary public event has the unchanged initialized source/key transfer loss, without an additional eligibility or digest-coherence premise. -/
theorem source_distance
    (bounded : ∀ publication, RegistrationNativePlatformPublicAdapterInterface.Respects mode budget (adversary publication))
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (target : Fin budget.accept × Fin budget.create) (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    ENNReal.ofReal ((actual configuration identityIndex serverKeyId rng bounds mode adversary budget previous decision).boolDistance
      (ideal configuration identityIndex serverKeyId bounds mode adversary budget previous decision target)) ≤
      loss configuration identityIndex serverKeyId bounds mode adversary budget previous decision target := by
  rw [actual_source configuration objects allocation identityIndex serverKeyId rng bounds mode adversary budget previous decision]
  exact RegistrationNativePlatformG3UniformOpaqueSource.source_distance setup checks wire route source (pure true) identityIndex serverKeyId target.1.val configuration.keyView configuration.sealFailure rawAllocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased helper writer bounds mode compiled observe
    configuration.agreement.representation correct functional budget
    (fun publication => RegistrationNativePlatformPublicAdapterInterface.compile_bound mode budget _ (bounded publication))
    target.2.succ previous candidate

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKeyTransfer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKeyTransfer.actual_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKeyTransfer.actual_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKeyTransfer.source_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKeyTransfer.source_distance

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreementGame
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreementCoverage
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditSecurity
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUnifiedStartupEd
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxResourceSecurity
/-! The actual source agreement failure is bounded on the same initialized public source profile. One common origin/cache exception and the actual recipient marker pay the original birthday, ordinary weak-EUF and create-times-accept KEM failure terms. Startup uses the configured original Ed generator with pure-true admission. -/
open CoreModels Aeneas OracleComp OracleSpec ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAgreementSecurity
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
variable {Value AD PT CT :Type}
variable (objects :AdapterServerConstructorObjects.Leaves configuration.views)
variable (ensureInit :StateT Unit ProbComp Bool)
variable (identityIndex :Nat) (identifier :U64) (rng :R)
variable (bounds :PqxdhDeploymentInterface.FreshBounds) (mode :PqxdhDeploymentInterface.Mode)
variable (adversary :RegistrationNativeExperiment.Public→OracleComp (RegistrationNativePlatformPublicAdapterInterface.ModeSpec mode) Value)
local notation "wire"=>RegistrationNativeConcreteCodec.wire
local notation "canonical"=>RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire

local notation "route"=>RegistrationNativePlatformPublicAdapterRouting.route
local notation "allocation"=>RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin
local notation "helper"=>RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame
local notation "writer"=>RegistrationNativePlatformConcreteSource.writer configuration.reservePackets
local notation "compiled"=>fun publication=>RegistrationNativePlatformPublicAdapterInterface.compile mode (adversary publication)

noncomputable def event (crypto :Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (publication :RegistrationNativeExperiment.Public) (value :Value×RegistrationNativeLedger.State)
    (stored :RegistrationNativePlatformPublicAdapterSourceEvents.State n KemSK R P) :Bool:=
  RegistrationNativePlatformPublicAdapterSourceAgreementGame.event (setup:=setup) crypto publication value stored

noncomputable def loss (previous :P) (budget :PqxdhDeploymentInterface.Budget) : ℝ≥0∞ :=
  RegistrationNativePlatformPublicAdapterAuditSecurity.loss (n:=n) configuration (pure true) identityIndex identifier bounds mode adversary previous budget+
    budget.create*budget.accept*RegistrationNativeRecipientFailure.failureRate setup

omit [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] [AdapterServerConstructorPrimitive.Standard] in
theorem exceptions_bound (previous :P) (budget :PqxdhDeploymentInterface.Budget)
    (bounded :∀publication,RegistrationNativePlatformPublicAdapterInterface.Respects mode budget (adversary publication))
    (functional :PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) :
    Pr{let result←RegistrationNativePlatformPublicAdapterSourceAgreementGame.experiment (n:=n) configuration ensureInit identityIndex identifier bounds mode adversary previous budget functional}[
      RegistrationNativePlatformOrdinaryKemExceptions.OriginCollision source (result.2.1.1.1,result.2.1.2) ∨result.2.2=true]≤
      RegistrationNativePlatformPublicAdapterAuditSecurity.loss (n:=n) configuration ensureInit identityIndex identifier bounds mode adversary previous budget+
        budget.create*budget.accept*RegistrationNativeRecipientFailure.failureRate setup :=by
  have original:=RegistrationNativePlatformOrdinaryKemExceptions.exceptions_bound (n:=n) setup checks wire route configuration.agreement.representation source ensureInit identityIndex identifier
    configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased
    helper writer bounds mode compiled previous budget
    (fun publication=>RegistrationNativePlatformPublicAdapterInterface.compile_bound mode budget _ (bounded publication)) functional
  have collision:=RegistrationNativePlatformIdentityCtxResourceSecurity.raw_bound (n:=n) setup checks wire route configuration.agreement.representation source
    configuration.keyView configuration.sealFailure allocation configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased
    helper writer ensureInit identityIndex identifier bounds mode compiled previous budget
    (fun publication=>RegistrationNativePlatformPublicAdapterInterface.compile_bound mode budget _ (bounded publication))
  exact original.trans (add_le_add (add_le_add collision le_rfl) le_rfl)

include objects in
theorem bound (crypto :Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (correct :configuration.keyView.Correct) (previous :P) (budget :PqxdhDeploymentInterface.Budget)
    (bounded :∀publication,RegistrationNativePlatformPublicAdapterInterface.Respects mode budget (adversary publication))
    (functional :PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) :
    Pr{let result←(RegistrationNativePlatformPublicAdapterExecution.profile (n:=n) configuration identityIndex identifier rng bounds mode adversary
      (event (setup:=setup) crypto)).run previous}[result.1=true]≤
      loss (n:=n) configuration identityIndex identifier bounds mode adversary previous budget :=by
  classical
  let startup:=RegistrationNativePlatformPublicAdapterUnifiedStartupEd.contract configuration
  have covered:=RegistrationNativePlatformPublicAdapterSourceAgreementGame.cover_experiment (n:=n) configuration objects (pure true) startup
    identityIndex identifier rng bounds mode adversary crypto previous budget bounded functional
  have included :
      Pr{let result←RegistrationNativePlatformPublicAdapterSourceAgreementGame.experiment (n:=n) configuration (pure true) identityIndex identifier bounds mode adversary previous budget functional}[
        ¬RegistrationNativePlatformPublicAdapterSourceAgreementGame.Holds configuration objects (pure true) startup identityIndex identifier rng bounds mode adversary crypto previous
          (result.2.1.1.1,result.2.1.2)]≤
      Pr{let result←RegistrationNativePlatformPublicAdapterSourceAgreementGame.experiment (n:=n) configuration (pure true) identityIndex identifier bounds mode adversary previous budget functional}[
        RegistrationNativePlatformOrdinaryKemExceptions.OriginCollision source (result.2.1.1.1,result.2.1.2) ∨result.2.2=true] :=by
    apply prEvent_mono_of_support
    intro result supported failed
    by_cases origin:RegistrationNativePlatformOrdinaryKemExceptions.OriginCollision source (result.2.1.1.1,result.2.1.2)
    · exact Or.inl origin
    · by_cases marker:result.2.2=true
      · exact Or.inr marker
      · exact (failed (RegistrationNativePlatformPublicAdapterSourceAgreementCoverage.coverage configuration objects (pure true) startup
          identityIndex identifier rng bounds mode adversary crypto correct previous budget bounded functional result supported origin marker)).elim
  exact covered.trans (included.trans (exceptions_bound (n:=n) configuration (pure true) identityIndex identifier bounds mode adversary previous budget bounded functional))

include objects in
/-- The original source event and loss are unchanged. Every already eligible good execution additionally carries the physical pre-record hash receipt and the exact consumed response-authentication digest for the same partner values. -/
theorem bound_with_session_ad (crypto :Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (correct :configuration.keyView.Correct) (previous :P) (budget :PqxdhDeploymentInterface.Budget)
    (bounded :∀publication,RegistrationNativePlatformPublicAdapterInterface.Respects mode budget (adversary publication))
    (functional :PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) :
    Pr{let result←(RegistrationNativePlatformPublicAdapterExecution.profile (n:=n) configuration identityIndex identifier rng bounds mode adversary
      (event (setup:=setup) crypto)).run previous}[result.1=true]≤
      loss (n:=n) configuration identityIndex identifier bounds mode adversary previous budget ∧
      ∀ (result : RegistrationNativeKemRecipientLogSource.Result KemSK
        (Option (RegistrationNativePlatformKemInitializedJournal.History n source Value P)×P) budget.create),
        result ∈ support (RegistrationNativePlatformPublicAdapterSourceAgreementGame.experiment (n:=n) configuration
          (pure true) identityIndex identifier bounds mode adversary previous budget functional) →
        ¬ RegistrationNativePlatformOrdinaryKemExceptions.OriginCollision source (result.2.1.1.1,result.2.1.2) →
        result.2.2 ≠ true →
        RegistrationNativePlatformPublicAdapterSourceAgreementGame.HoldsWithSessionAd configuration objects (pure true)
          (RegistrationNativePlatformPublicAdapterUnifiedStartupEd.contract configuration)
          identityIndex identifier rng bounds mode adversary crypto previous (result.2.1.1.1,result.2.1.2) := by
  refine ⟨bound configuration objects identityIndex identifier rng bounds mode adversary crypto correct previous budget bounded functional, ?_⟩
  intro result supported origin marker
  exact RegistrationNativePlatformPublicAdapterSourceAgreementCoverage.coverage_with_session_ad configuration objects (pure true)
    (RegistrationNativePlatformPublicAdapterUnifiedStartupEd.contract configuration)
    identityIndex identifier rng bounds mode adversary crypto correct previous budget bounded functional result supported origin marker

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAgreementSecurity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAgreementSecurity.exceptions_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAgreementSecurity.exceptions_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAgreementSecurity.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAgreementSecurity.bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAgreementSecurity.bound_with_session_ad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAgreementSecurity.bound_with_session_ad

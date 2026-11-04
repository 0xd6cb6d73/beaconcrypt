-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreement
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKemHistory
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterUniversalObservation
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterKemObservationProbability
/-! The agreement event is evaluated on the actual initialized source operation log. Its common-sample probability law consumes the concrete source execution theorem and reads neither a reconstructed native transcript nor an existential compatible source log. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreementGame
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
variable (serverEd :AdapterServerConstructorJoint.EdContract configuration.generator configuration.view setup.joint (AdapterServerConstructorStartup.edCore ensureInit))
variable (identityIndex :Nat) (identifier :U64) (rng :R)
variable (bounds :PqxdhDeploymentInterface.FreshBounds) (mode :PqxdhDeploymentInterface.Mode)
variable (adversary :RegistrationNativeExperiment.Public→OracleComp (RegistrationNativePlatformPublicAdapterInterface.ModeSpec mode) Value)
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "AuditState"=>RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source
local notation "wire"=>RegistrationNativeConcreteCodec.wire
local notation "canonical"=>RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "codec"=>RegistrationNativeWire.ledgerCodec canonical


noncomputable def event (crypto :Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (publication :RegistrationNativeExperiment.Public) (_value :Value×RegistrationNativeLedger.State)
    (stored :RegistrationNativePlatformPublicAdapterSourceEvents.State n KemSK R P) :Bool:=
  RegistrationNativePlatformPublicAdapterSourceAgreement.flag crypto setup.source publication.mldsaPublic stored.backend.2.2

def Failure (crypto :Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT) :
    RegistrationNativePlatformPublicAdapterKemHistory.Outcome (n:=n) (Value:=Value) configuration→Prop
  | none=>False
  | some ⟨initial,result⟩=>¬RegistrationNativePlatformPublicAdapterSourceAgreement.AllOwners crypto setup.source initial.public.mldsaPublic result.2.2

omit [AdapterServerConstructorPrimitive.Standard] [PublicWrapperPlatform.CryptoOperations] [FrameDispatchFallback.Operations] in
theorem observe_failure (crypto :Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (previous :P) (outcome :RegistrationNativePlatformPublicAdapterKemHistory.Outcome (n:=n) (Value:=Value) configuration) :
    (RegistrationNativePlatformPublicAdapterKemHistory.observe configuration previous (event (setup:=setup) crypto) outcome).1=true ↔
      Failure configuration crypto outcome :=by
  cases outcome with
  | none=>simp only [RegistrationNativePlatformPublicAdapterKemHistory.observe,Failure,Bool.false_eq_true]
  | some selected=>
    obtain ⟨initial,result⟩:=selected
    change RegistrationNativePlatformPublicAdapterSourceAgreement.flag crypto setup.source initial.public.mldsaPublic result.2.2=true ↔_
    exact RegistrationNativePlatformPublicAdapterSourceAgreement.flag_iff crypto setup.source initial.public.mldsaPublic result.2.2

include objects serverEd in
theorem probability (crypto :Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT) (previous :P) :
    Pr{let outcome←(RegistrationNativePlatformPublicAdapterExecution.profile (n:=n) configuration identityIndex identifier rng bounds mode adversary
      (event (setup:=setup) crypto)).run previous}[outcome.1=true]=
    Pr{let outcome←RegistrationNativePlatformPublicAdapterKemHistory.sample (n:=n) configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary previous}[
      Failure configuration crypto outcome] :=by
  rw [←RegistrationNativePlatformPublicAdapterKemHistory.source_profile configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary previous
    (event (setup:=setup) crypto),prEvent_map]
  apply prEvent_congr
  intro outcome
  exact observe_failure configuration crypto previous outcome

noncomputable def native (previous :P) :=
  RegistrationNativePlatformOrdinaryKemHistorySource.native (n:=n) setup checks wire RegistrationNativePlatformPublicAdapterRouting.route
    configuration.agreement.representation source ensureInit identityIndex identifier configuration.keyView configuration.sealFailure
    (RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin)
    configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased
    (RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame)
    (RegistrationNativePlatformConcreteSource.writer configuration.reservePackets) bounds mode
    (fun publication=>RegistrationNativePlatformPublicAdapterInterface.compile mode (adversary publication)) previous

def Holds (crypto :Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT) (previous :P)
    (observation :RegistrationNativePlatformPublicAdapterKemHistory.Observed (n:=n) (KemSK:=KemSK) (source:=source) (P:=P) (Value:=Value)) :Prop:=
  ∀outcome,outcome∈support (RegistrationNativePlatformPublicAdapterKemHistory.sample (n:=n) configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary previous)→
    RegistrationNativePlatformPublicAdapterKemHistory.project configuration previous outcome=observation→¬Failure configuration crypto outcome

include objects serverEd in
theorem cover (crypto :Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT) (previous :P) :
    Pr{let outcome←(RegistrationNativePlatformPublicAdapterExecution.profile (n:=n) configuration identityIndex identifier rng bounds mode adversary
      (event (setup:=setup) crypto)).run previous}[outcome.1=true]≤
    Pr{let observation←native (n:=n) configuration ensureInit identityIndex identifier bounds mode adversary previous}[
      ¬Holds configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary crypto previous observation] :=by
  rw [probability configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary crypto previous]
  apply RegistrationNativePlatformPublicAdapterUniversalObservation.bound
    (RegistrationNativePlatformPublicAdapterKemHistory.sample (n:=n) configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary previous)
    (native (n:=n) configuration ensureInit identityIndex identifier bounds mode adversary previous)
    (RegistrationNativePlatformPublicAdapterKemHistory.project configuration previous) id
  · rw [id_map]
    exact RegistrationNativePlatformPublicAdapterKemHistory.native configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary previous
  · intro outcome supported observation _possible same failed clean
    exact clean outcome supported same failed

noncomputable def experiment (previous :P) (budget :PqxdhDeploymentInterface.Budget)
    (functional :PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) :=
  RegistrationNativePlatformOrdinaryKemInitializedJournal.experiment (n:=n) setup checks wire RegistrationNativePlatformPublicAdapterRouting.route
    configuration.agreement.representation source ensureInit identityIndex identifier configuration.keyView configuration.sealFailure
    (RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin)
    configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased
    (RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame)
    (RegistrationNativePlatformConcreteSource.writer configuration.reservePackets) bounds mode
    (fun publication=>RegistrationNativePlatformPublicAdapterInterface.compile mode (adversary publication)) previous budget functional

include objects serverEd in
theorem cover_experiment (crypto :Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT) (previous :P)
    (budget :PqxdhDeploymentInterface.Budget)
    (bounded :∀publication,RegistrationNativePlatformPublicAdapterInterface.Respects mode budget (adversary publication))
    (functional :PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem) :
    Pr{let outcome←(RegistrationNativePlatformPublicAdapterExecution.profile (n:=n) configuration identityIndex identifier rng bounds mode adversary
      (event (setup:=setup) crypto)).run previous}[outcome.1=true]≤
    Pr{let result←experiment (n:=n) configuration ensureInit identityIndex identifier bounds mode adversary previous budget functional}[
      ¬Holds configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary crypto previous (result.2.1.1.1,result.2.1.2)] :=by
  have estimate:=cover (n:=n) configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary crypto previous
  have same:=RegistrationNativePlatformPublicAdapterKemObservationProbability.source_probability (n:=n) configuration ensureInit identityIndex identifier
    bounds mode adversary previous budget bounded functional
    (fun observation=>¬Holds configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary crypto previous observation)
  exact estimate.trans_eq same.symm

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreementGame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreementGame.observe_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreementGame.observe_failure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreementGame.probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreementGame.probability

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreementGame.cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreementGame.cover

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreementGame.cover_experiment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceAgreementGame.cover_experiment

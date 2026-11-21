-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordIdeal
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordTraceView
import BeaconcryptCore.Computational.RegistrationNativePlatformLorRecordObserver
import BeaconcryptCore.Computational.RegistrationNativePlatformWeightedRecordTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryObserverSecurity
import BeaconcryptCore.Computational.RegistrationNativeCanonicalCoverage
/-! Same-result descriptor receipts attach original warm source observers to their native physical ideal baselines. The source designation receipt is supplied separately; neither runtime identity nor real-to-ideal support inclusion is used. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordObserverIdeal
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicRecordOpaqueInitialized (Context prior)
variable {I KemSK Platform E Value : Type} {base : OracleSpec I}
private theorem ledger_event {cap : Nat} {ProviderState : Type} (source : RegistrationNativeMldsa.Source)
    (observe : Value × RegistrationNativeLedger.State → Bool) :
    RegistrationNativePlatformG3UniformOpaqueRecord.event (cap := cap) (KemSK := KemSK) (ProviderState := ProviderState) (Platform := Platform)
      source (fun value _produced _raw => observe value) =
    RegistrationNativeSelectedRecordTrace.viewSelected (n := cap)
      (E := RegistrationNativePlatformSelectiveEntropyEnvironment.State cap KemSK ProviderState Platform source) observe := by
  funext record
  rcases record with ⟨outcome,produced,raw,slots⟩
  cases outcome <;> rfl

attribute [local irreducible] RegistrationNativeRecordPackage.ctx RegistrationNativePlatformG3UniformRecordProgram.program
  RegistrationNativePlatformG3UniformRecordTraceView.run

variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
open RegistrationNativePlatformG3UniformRecordProgram (Sample)
variable (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create+1)) (previous : Platform)
local notation "cap" => budget.cap 4+budget.cap 5
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "whole" => RegistrationNativePlatformG3UniformRecordIdeal.run setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds adversary budget selected previous
local notation "traced" => RegistrationNativePlatformG3UniformRecordTraceView.run setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds adversary budget selected previous (fun _ => PqxdhRecordLiftIdeal.KeyMode.random)
local notation "TraceView" => RegistrationNativeRecordPackage.View cap (RegistrationNativePlatformSelectiveRecordTraceStartup.Extra cap KemSK RegistrationNativeKemSwitchSource.Phase Platform source) Value
local notation "ideal(" observe ")" => RegistrationNativePlatformOrdinaryObserverSecurity.ideal setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds PqxdhDeploymentInterface.Mode.P adversary budget selected previous observe

/-- Per-result source designation and the derived physical storage receipt remove the hidden-test conjunct in the complete warm ideal game. -/
theorem lor_of_selected (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
    (target : Fin budget.accept × Fin budget.capacity)
    (designation : ∀ (parameters : Sample KemSK cap) (observed : TraceView), (parameters,observed) ∈ support traced →
      ∀ finished ∈ observed.result,
        RegistrationNativeLorCanonical.GoodAt setup.source.crypto canonical serverKeyId budget filter target finished.2.1 →
        RegistrationNativeLorSelectedTests.TestsSelected setup.source.crypto canonical serverKeyId finished.2.1.2 finished.2.2.2.events
          (RegistrationNativePlatformInstallKernelStorage.Selected setup parameters.seed parameters.scalar parameters.candidate)) :
    𝒟[ideal(RegistrationNativeLorRecordSecurity.observer setup.source.crypto canonical serverKeyId budget filter guess target true)] {true} =
      2⁻¹ * 𝒟[ideal(RegistrationNativeLorRecordSecurity.observer setup.source.crypto canonical serverKeyId budget filter guess target false)] {true} := by
  have attachment (winning : Bool) :
      𝒟[ideal(RegistrationNativeLorRecordSecurity.observer setup.source.crypto canonical serverKeyId budget filter guess target winning)] {true} =
      𝒟[RegistrationNativeLorRecordSecurity.recordObserver setup.source.crypto canonical serverKeyId budget filter guess target winning <$> whole] {true} := by
    simp only [RegistrationNativePlatformOrdinaryObserverSecurity.ideal,RegistrationNativePlatformG3UniformRecordSource.ideal,
      ledger_event,RegistrationNativePlatformG3UniformRecordIdeal.run]
    rw [←RegistrationNativePlatformG3UniformRecordTraceView.ctx_erase setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds adversary budget selected previous (fun _ => PqxdhRecordLiftIdeal.KeyMode.random)]
    simp only [Functor.map_map,←prEvent_eq_evalDist_singleton _ true]
    apply prEvent_congr_of_support
    rintro ⟨parameters,observed⟩ supported
    rw [RegistrationNativePlatformLorRecordObserver.observer_source setup canonical serverKeyId parameters.seed parameters.scalar parameters.candidate
      budget filter guess target winning observed
      (RegistrationNativePlatformG3UniformRecordTraceView.hidden setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds adversary budget selected previous (fun _ => PqxdhRecordLiftIdeal.KeyMode.random) parameters observed supported)
      (designation parameters observed supported)]
  rw [attachment true,attachment false]
  change 𝒟[(fun observed => RegistrationNativeLorRecordSecurity.recordObserver setup.source.crypto canonical serverKeyId budget filter guess target true observed) <$> whole] {true} =
    2⁻¹ * 𝒟[(fun observed => RegistrationNativeLorRecordSecurity.recordObserver setup.source.crypto canonical serverKeyId budget filter guess target false observed) <$> whole] {true}
  simp only [RegistrationNativeLorRecordSecurity.recordObserver,Bool.false_eq_true,ite_true,ite_false]
  exact RegistrationNativePlatformG3UniformRecordIdeal.lor setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds adversary budget selected previous filter guess target

/-- Original good-selector source claims attach to the same hidden fresh handle, retaining one warm selector probability. -/
theorem fresh_bytes_of_claimed (claim : Value → Option (Nat × Pqxdh.Bytes))
    (target : RegistrationNativeCanonicalSelector.Target budget)
    (designation : ∀ (parameters : Sample KemSK cap) (observed : TraceView), (parameters,observed) ∈ support traced →
      ∀ finished ∈ observed.result,
        RegistrationNativePrekeyEvents.GoodAt setup.source.crypto canonical serverKeyId budget target claim (finished.2.1.1,(finished.2.1.2,())) →
        RegistrationNativeInstallTarget.Claimed claim finished.2.1.1 finished.2.1.2 finished.2.2.2.events
          (RegistrationNativePlatformInstallKernelStorage.Selected setup parameters.seed parameters.scalar parameters.candidate)) :
    𝒟[ideal(RegistrationNativeCanonicalCoverage.decision setup.source.crypto canonical serverKeyId budget claim target)] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ * 𝒟[ideal(fun actual => RegistrationNativeCanonicalSelector.selected setup.source.crypto canonical serverKeyId budget claim target actual.1 actual.2)] {true} := by
  have attachment :
      𝒟[ideal(RegistrationNativeCanonicalCoverage.decision setup.source.crypto canonical serverKeyId budget claim target)] {true} ≤
      𝒟[RegistrationNativeWeightedRecordView.winning setup.source.crypto canonical serverKeyId budget claim target <$> whole] {true} := by
    simp only [RegistrationNativePlatformOrdinaryObserverSecurity.ideal,RegistrationNativePlatformG3UniformRecordSource.ideal,
      ledger_event,RegistrationNativePlatformG3UniformRecordIdeal.run]
    rw [←RegistrationNativePlatformG3UniformRecordTraceView.ctx_erase setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds adversary budget selected previous (fun _ => PqxdhRecordLiftIdeal.KeyMode.random)]
    simp only [Functor.map_map,←prEvent_eq_evalDist_singleton _ true]
    apply prEvent_mono_of_support
    rintro ⟨parameters,observed⟩ supported hit
    cases outcome : observed.result with
    | none => simp only [RegistrationNativePlatformSelectiveRecordTraceView.erase,RegistrationNativePlatformSelectiveRecordTraceStartup.forget,
        RegistrationNativeSelectedRecordTrace.viewSelected,RegistrationNativeSelectedRecordTrace.outcomeSelected,outcome,Option.map_none,Option.elim_none,Bool.false_eq_true] at hit
    | some finished =>
      have present : finished ∈ observed.result := by simp only [outcome,Option.mem_some_iff]
      have good : RegistrationNativeCanonicalCoverage.GoodSelectedAt setup.source.crypto canonical serverKeyId budget claim target (finished.2.1.1,(finished.2.1.2,())) := by
        simpa only [RegistrationNativePlatformSelectiveRecordTraceView.erase,RegistrationNativePlatformSelectiveRecordTraceStartup.forget,
          RegistrationNativeSelectedRecordTrace.viewSelected,RegistrationNativeSelectedRecordTrace.outcomeSelected,outcome,Option.map_some,Option.elim_some,
          RegistrationNativeCanonicalCoverage.decision,RegistrationNativeCanonicalCoverage.event,decide_eq_true_eq] using hit
      exact RegistrationNativePlatformWeightedRecordTrace.view_winning setup canonical serverKeyId parameters.seed parameters.scalar parameters.candidate claim budget target observed
        (RegistrationNativePlatformG3UniformRecordTraceView.hidden setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds adversary budget selected previous (fun _ => PqxdhRecordLiftIdeal.KeyMode.random) parameters observed supported)
        ⟨finished,present,designation parameters observed supported finished present good.1,good.2⟩
  have baseline := RegistrationNativePlatformG3UniformRecordIdeal.fresh_bytes setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds adversary budget selected previous claim target
  have selectorSource : ideal(fun actual => RegistrationNativeCanonicalSelector.selected setup.source.crypto canonical serverKeyId budget claim target actual.1 actual.2) =
      RegistrationNativeWeightedRecordView.selection setup.source.crypto canonical serverKeyId budget claim target <$> whole := by
    simp only [RegistrationNativePlatformOrdinaryObserverSecurity.ideal,RegistrationNativePlatformG3UniformRecordSource.ideal,ledger_event,RegistrationNativePlatformG3UniformRecordIdeal.run]
    rfl
  rw [selectorSource]
  exact attachment.trans baseline

end BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordObserverIdeal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordObserverIdeal.lor_of_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordObserverIdeal.lor_of_selected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordObserverIdeal.fresh_bytes_of_claimed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformRecordObserverIdeal.fresh_bytes_of_claimed

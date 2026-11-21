-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorRecordTrace
import BeaconcryptCore.Computational.RegistrationNativeLorRecordSecurity
/-! The literal original winning or eligibility observer equals the physical record observer when its same-result public selected receipts are attached to the current source trace's hidden slots. This local step retains the original bit, ledger and platform result; the separate source designation theorem supplies its selected receipts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorRecordObserver
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeRecordPackage (View)
open RegistrationNativePlatformSelectiveRecordTraceStartup (Extra)
open RegistrationNativePlatformInstallKernelStorage (Selected)
variable {n : Nat} {I KemSK ProviderState Platform Value : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

/-- Same-result source designation and physical storage remove the hidden-test conjunct without narrowing the original observer. -/
theorem observer_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (serverKeyId : Std.U64)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (budget : PqxdhDeploymentInterface.Budget) (filter : RegistrationNativeLorEvents.Filter Value) (guess : Value → Bool)
    (target : Fin budget.accept × Fin budget.capacity) (winning : Bool)
    (observed : View n (Extra n KemSK ProviderState Platform source) Value)
    (hidden : RegistrationNativePlatformSelectiveRecordTraceView.Hidden setup seed scalar candidate observed)
    (selected : ∀ finished ∈ observed.result,
      RegistrationNativeLorCanonical.GoodAt setup.source.crypto wire serverKeyId budget filter target finished.2.1 →
      RegistrationNativeLorSelectedTests.TestsSelected setup.source.crypto wire serverKeyId finished.2.1.2
        finished.2.2.2.events (Selected setup seed scalar candidate)) :
    RegistrationNativeLorRecordSecurity.recordObserver setup.source.crypto wire serverKeyId budget filter guess target winning
      (RegistrationNativePlatformSelectiveRecordTraceView.erase observed) =
    RegistrationNativeSelectedRecordTrace.viewSelected
      (RegistrationNativeLorRecordSecurity.observer setup.source.crypto wire serverKeyId budget filter guess target winning)
      (RegistrationNativePlatformSelectiveRecordTraceView.erase observed) := by
  apply Bool.eq_iff_iff.mpr
  rw [RegistrationNativeLorRecordSecurity.record_event]
  constructor
  · exact And.right
  · intro seen
    refine ⟨?_,seen⟩
    cases outcome : observed.result with
    | none =>
      simp only [RegistrationNativeSelectedRecordTrace.viewSelected,RegistrationNativeSelectedRecordTrace.outcomeSelected,
        RegistrationNativePlatformSelectiveRecordTraceView.erase,RegistrationNativePlatformSelectiveRecordTraceStartup.forget,
        outcome,Option.map_none,Option.elim_none] at seen
      cases seen
    | some finished =>
      have present : finished ∈ observed.result := by simp only [outcome,Option.mem_some_iff]
      have eligible := RegistrationNativeLorRecordSecurity.observer_good setup.source.crypto wire serverKeyId budget filter guess target winning finished.2.1 (by
        simpa only [RegistrationNativeSelectedRecordTrace.viewSelected,RegistrationNativeSelectedRecordTrace.outcomeSelected,
          RegistrationNativePlatformSelectiveRecordTraceView.erase,RegistrationNativePlatformSelectiveRecordTraceStartup.forget,
          outcome,Option.map_some,Option.elim_some] using seen)
      exact RegistrationNativePlatformLorRecordTrace.view_tests setup wire serverKeyId seed scalar candidate observed hidden
        ⟨finished,present,selected finished present eligible⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformLorRecordObserver
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorRecordObserver.observer_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorRecordObserver.observer_source

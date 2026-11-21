-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceView
import BeaconcryptCore.Computational.RegistrationNativeInstallTarget
import BeaconcryptCore.Computational.RegistrationNativeWeightedRecordView
/-! A claimed selected descriptor in the same actual source trace attaches to its literal hidden fresh handle. Functional public selection is retained on that same full ledger, with the native/platform state preserved by chronology erasure. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformWeightedRecordTrace
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeRecordPackage (View)
open RegistrationNativePlatformSelectiveRecordTraceStartup (Extra)
open RegistrationNativePlatformInstallKernelStorage (Selected)
variable {n : Nat} {I KemSK ProviderState Platform Value : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}


/-- A selected descriptor for the original claimed entry gives the same actual hidden fresh hit. -/
theorem view_fresh (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : View n (Extra n KemSK ProviderState Platform source) Value)
    (hidden : RegistrationNativePlatformSelectiveRecordTraceView.Hidden setup seed scalar candidate observed)
    (selected : ∃ finished ∈ observed.result,
      RegistrationNativeInstallTarget.Claimed claim finished.2.1.1 finished.2.1.2 finished.2.2.2.events (Selected setup seed scalar candidate)) :
    RegistrationNativeRecordViewFresh.FreshHit claim (RegistrationNativePlatformSelectiveRecordTraceView.erase observed) := by
  obtain ⟨finished,present,claimed⟩ := selected
  have outcome : observed.result = some finished := by simpa only [Option.mem_def] using present
  obtain ⟨index,guess,entry,claimAt,fresh,guessed,slot⟩ := RegistrationNativeInstallTarget.hidden claim finished.2.1.1
    finished.2.1.2 finished.2.2.2.events (Selected setup seed scalar candidate) observed.slots claimed (hidden finished present)
  refine ⟨(finished.1,finished.2.1,finished.2.2.1),?_,index,guess,entry,claimAt,fresh,slot,guessed⟩
  simp only [RegistrationNativePlatformSelectiveRecordTraceView.erase,RegistrationNativePlatformSelectiveRecordTraceStartup.forget,
    outcome,Option.map_some,Option.mem_some_iff]

/-- The public selector remains on the same ledger when the selected original claim attaches to its physical hidden handle. -/
theorem view_winning (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (serverKeyId : Std.U64)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (budget : PqxdhDeploymentInterface.Budget) (target : RegistrationNativeCanonicalSelector.Target budget)
    (observed : View n (Extra n KemSK ProviderState Platform source) Value)
    (hidden : RegistrationNativePlatformSelectiveRecordTraceView.Hidden setup seed scalar candidate observed)
    (selected : ∃ finished ∈ observed.result,
      RegistrationNativeInstallTarget.Claimed claim finished.2.1.1 finished.2.1.2 finished.2.2.2.events (Selected setup seed scalar candidate) ∧
      RegistrationNativeCanonicalSelector.selected setup.source.crypto wire serverKeyId budget claim target finished.2.1.1 finished.2.1.2 = true) :
    RegistrationNativeWeightedRecordView.winning setup.source.crypto wire serverKeyId budget claim target
      (RegistrationNativePlatformSelectiveRecordTraceView.erase observed) = true := by
  classical
  obtain ⟨finished,present,claimed,chosen⟩ := selected
  have fresh := view_fresh setup seed scalar candidate claim observed hidden ⟨finished,present,claimed⟩
  have outcome : observed.result = some finished := by simpa only [Option.mem_def] using present
  have selector : RegistrationNativeWeightedRecordView.selection setup.source.crypto wire serverKeyId budget claim target
      (RegistrationNativePlatformSelectiveRecordTraceView.erase observed) = true := by
    simpa only [RegistrationNativeWeightedRecordView.selection,RegistrationNativeSelectedRecordTrace.viewSelected,
      RegistrationNativeSelectedRecordTrace.outcomeSelected,RegistrationNativePlatformSelectiveRecordTraceView.erase,
      RegistrationNativePlatformSelectiveRecordTraceStartup.forget,outcome,Option.map_some,Option.elim_some] using chosen
  simpa only [RegistrationNativeWeightedRecordView.winning,RegistrationNativeRecordViewFresh.event,Bool.and_eq_true,decide_eq_true_eq] using And.intro selector fresh

end BeaconcryptCore.Computational.RegistrationNativePlatformWeightedRecordTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformWeightedRecordTrace.view_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformWeightedRecordTrace.view_fresh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformWeightedRecordTrace.view_winning' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformWeightedRecordTrace.view_winning

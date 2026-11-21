-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveRecordTraceView
import BeaconcryptCore.Computational.RegistrationNativeLorRecordTrace
/-! Same-result public selected installation receipts attach to the current source's derived physical hidden slots. This logical observer step keeps the original full ledger and platform state; public designation itself is discharged by the separate actual source provenance port. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorRecordTrace
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeRecordPackage (View)
open RegistrationNativePlatformSelectiveRecordTraceStartup (Extra)
open RegistrationNativePlatformInstallKernelStorage (Selected)
variable {n : Nat} {I KemSK ProviderState Platform Value : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

/-- The actual same-trace physical invariant attaches every selected admitted test to its same hidden handle. -/
theorem view_tests (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (serverKeyId : Std.U64)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (observed : View n (Extra n KemSK ProviderState Platform source) Value)
    (hidden : RegistrationNativePlatformSelectiveRecordTraceView.Hidden setup seed scalar candidate observed)
    (selected : ∃ finished ∈ observed.result,
      RegistrationNativeLorSelectedTests.TestsSelected setup.source.crypto wire serverKeyId finished.2.1.2
        finished.2.2.2.events (Selected setup seed scalar candidate)) :
    RegistrationNativeLorRecordTrace.TestsHidden setup.source.crypto wire serverKeyId
      (RegistrationNativePlatformSelectiveRecordTraceView.erase observed) := by
  obtain ⟨finished,present,chosen⟩ := selected
  have outcome : observed.result = some finished := by simpa only [Option.mem_def] using present
  have origin := hidden finished present
  refine ⟨(finished.1,finished.2.1,finished.2.2.1),?_,?_⟩
  · simp only [RegistrationNativePlatformSelectiveRecordTraceView.erase,RegistrationNativePlatformSelectiveRecordTraceStartup.forget,
      outcome,Option.map_some,Option.mem_some_iff]
  · intro pre entry post handle left right split query admitted
    obtain ⟨role,ordinal,message,paired,chosenInput⟩ := chosen pre entry post handle left right split query admitted
    exact origin role ordinal message handle paired chosenInput

end BeaconcryptCore.Computational.RegistrationNativePlatformLorRecordTrace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorRecordTrace.view_tests' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorRecordTrace.view_tests

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallLedgerInterface
import BeaconcryptCore.Computational.RegistrationNativeRawAdapter

/-! The actual raw adapter forwards the complete typed poststate, including failure and malformed-input branches. Typed safety and physical hidden-slot persistence therefore compose through the raw adapter's literal AST. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallRawStorage
open RegistrationNativeInstallLedger (Storage Forward forward_trans)
variable {n : Nat} {NativeState : Type}

/-- Actual raw decoding preserves typed validity and every already hidden physical handle. -/
theorem raw (typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT NativeState ProbComp))
    (wire : RegistrationNativeWire.Wire)
    (slots : NativeState → PqxdhDeploymentInterface.Handle → Option (PqxdhRecordLiftInterface.Slot n))
    (valid : NativeState → Prop)
    (storage : ∀ query before result, valid before → result ∈ support ((typed query).run before) →
      Storage slots valid before result.2)
    (query : RegistrationNativeInterface.Spec.Domain) (before : NativeState)
    (result : RegistrationNativeInterface.Spec.Range query × NativeState) (prior : valid before)
    (supported : result ∈ support ((RegistrationNativeRawAdapter.handler wire typed query).run before)) :
    Storage slots valid before result.2 := by
  apply simulateQ_run_preserves_inv_of_query typed
    (fun current => Storage slots valid before current) _
    (RegistrationNativeRawAdapter.adapter wire query) before ⟨prior, fun _ present => present⟩ result supported
  intro request current good answer reached
  have stepped := storage request current answer good.1 reached
  exact ⟨stepped.1, forward_trans slots before current answer.2 good.2 stepped.2⟩

end BeaconcryptCore.Computational.RegistrationNativeInstallRawStorage
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallRawStorage.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallRawStorage.raw

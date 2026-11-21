-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMaterialBudget

/-! Original native accept and finish command bills bound root preparations without counting primitive loops. Raw parse failures and terminal-abort finishes retain their original class allowance. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativePreparationBudget
variable {Value : Type}

def IsPreparing (query : RegistrationNativeRawAdapter.TypedSpec.Domain) : Prop :=
  RegistrationNativeRawAdapter.kind query = 3 ∨ RegistrationNativeRawAdapter.kind query = 5
instance : DecidablePred IsPreparing := inferInstanceAs (DecidablePred fun query =>
  RegistrationNativeRawAdapter.kind query = 3 ∨ RegistrationNativeRawAdapter.kind query = 5)

def allowance (bounds : PqxdhDeploymentInterface.FreshBounds) (budget : PqxdhDeploymentInterface.Budget) : Nat :=
  (∑ full, PqxdhDeploymentCompileSecrecy.wrapCost bounds 3 full * budget.cap full) +
    (∑ full, PqxdhDeploymentCompileSecrecy.wrapCost bounds 5 full * budget.cap full)

/-- Hidden-test and fresh-byte bookkeeping add no root preparation. -/
theorem allowance_eq (bounds : PqxdhDeploymentInterface.FreshBounds) (budget : PqxdhDeploymentInterface.Budget) :
    allowance bounds budget = budget.cap 3 + budget.cap 5 := by
  simp [allowance, Fin.sum_univ_succ, PqxdhDeploymentCompileSecrecy.wrapCost]

/-- The actual full raw-CE compiler preserves the original accept-plus-finish allowance. -/
theorem compile_bound (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : Aeneas.Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work) :
    (RegistrationNativeFullCompiler.compile crypto wire serverKeyId bounds mode work).IsQueryBoundP IsPreparing
      (allowance bounds budget) :=
  RegistrationNativeMaterialBudget.union_bound _ _ _ _ _
    (RegistrationNativeFullCompiler.compile_bound crypto wire serverKeyId bounds mode work budget bounded 3)
    (RegistrationNativeFullCompiler.compile_bound crypto wire serverKeyId bounds mode work budget bounded 5)

end BeaconcryptCore.Computational.RegistrationNativePreparationBudget

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePreparationBudget.allowance_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePreparationBudget.allowance_eq

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePreparationBudget.compile_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePreparationBudget.compile_bound

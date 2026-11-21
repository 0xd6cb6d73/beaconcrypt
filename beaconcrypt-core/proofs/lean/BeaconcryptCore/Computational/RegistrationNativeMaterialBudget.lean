-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeFullCompiler

/-! The unchanged original CE budget bounds the union of actual native build and finish commands. This bill counts their sum once, including parse failures and cancelled operations. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeMaterialBudget
variable {Index Value : Type} {spec : OracleSpec Index}

/-- Two structural class bills bound their union without another scheduling factor. -/
theorem union_bound (work : OracleComp spec Value) (left right : Index → Prop)
    [DecidablePred left] [DecidablePred right] (first second : Nat)
    (leftBound : work.IsQueryBoundP left first) (rightBound : work.IsQueryBoundP right second) :
    work.IsQueryBoundP (fun query => left query ∨ right query) (first + second) := by
  induction work using OracleComp.inductionOn generalizing first second with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at leftBound rightBound ⊢
      refine ⟨?_, fun reply => ?_⟩
      · by_cases selectedLeft : left query <;> by_cases selectedRight : right query <;>
          simp_all
      · apply (ih reply _ _ (leftBound.2 reply) (rightBound.2 reply)).mono
        by_cases selectedLeft : left query <;> by_cases selectedRight : right query <;>
          simp_all <;> omega

def IsMaterial (query : RegistrationNativeRawAdapter.TypedSpec.Domain) : Prop :=
  RegistrationNativeRawAdapter.kind query = 4 ∨ RegistrationNativeRawAdapter.kind query = 5
instance : DecidablePred IsMaterial := inferInstanceAs (DecidablePred fun query =>
  RegistrationNativeRawAdapter.kind query = 4 ∨ RegistrationNativeRawAdapter.kind query = 5)

def allowance (bounds : PqxdhDeploymentInterface.FreshBounds) (budget : PqxdhDeploymentInterface.Budget) : Nat :=
  (∑ full, PqxdhDeploymentCompileSecrecy.wrapCost bounds 4 full * budget.cap full) +
    (∑ full, PqxdhDeploymentCompileSecrecy.wrapCost bounds 5 full * budget.cap full)

/-- Hidden-test and fresh-byte bookkeeping add no registration material demand. -/
theorem allowance_eq (bounds : PqxdhDeploymentInterface.FreshBounds) (budget : PqxdhDeploymentInterface.Budget) :
    allowance bounds budget = budget.cap 4 + budget.cap 5 := by
  simp [allowance, Fin.sum_univ_succ, PqxdhDeploymentCompileSecrecy.wrapCost]

/-- The actual full raw-CE compiler preserves the original build-plus-finish allowance. -/
theorem compile_bound (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : Aeneas.Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work) :
    (RegistrationNativeFullCompiler.compile crypto wire serverKeyId bounds mode work).IsQueryBoundP IsMaterial
      (allowance bounds budget) :=
  union_bound _ _ _ _ _
    (RegistrationNativeFullCompiler.compile_bound crypto wire serverKeyId bounds mode work budget bounded 4)
    (RegistrationNativeFullCompiler.compile_bound crypto wire serverKeyId bounds mode work budget bounded 5)

end BeaconcryptCore.Computational.RegistrationNativeMaterialBudget
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMaterialBudget.union_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMaterialBudget.union_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMaterialBudget.compile_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMaterialBudget.compile_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMaterialBudget.allowance_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMaterialBudget.allowance_eq

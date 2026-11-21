-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEntropyBounds
import BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendCallbackBudget
open PqxdhDeploymentInterface (FullSpec Mode Budget queryClass)
variable {Q A : Type} {spec : OracleSpec Q}
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

def Sending (query : FullSpec.Domain) : Prop :=
  queryClass query=8 ∨queryClass query=10 ∨queryClass query=12 ∨queryClass query=13
noncomputable instance : DecidablePred Sending :=fun _=>inferInstance

private theorem union_bound (first second : spec.Domain → Prop) [DecidablePred first] [DecidablePred second]
    (work : OracleComp spec A) (left right : Nat)
    (firstCap : work.IsQueryBoundP first left) (secondCap : work.IsQueryBoundP second right) :
    work.IsQueryBoundP (fun query=>first query ∨second query) (left+right) := by
  induction work using OracleComp.inductionOn generalizing left right with
  | pure value=>trivial
  | query_bind query next ih=>
    rw [isQueryBoundP_query_bind_iff] at firstCap secondCap ⊢
    constructor
    · by_cases a : first query <;>by_cases b : second query <;>simp_all only [not_true_eq_false,not_false_eq_true,false_or,or_false,true_or,or_true] <;>omega
    · intro reply
      apply (ih reply _ _ (firstCap.2 reply) (secondCap.2 reply)).mono
      by_cases a : first query <;>by_cases b : second query <;>simp_all only [ite_true,ite_false,true_or,or_true,false_or,or_false,not_true_eq_false,not_false_eq_true] <;>omega

/-- All send-producing public attempts consume their original combined allowance, including rejected test/fresh requests and failed sends. -/
theorem bound (work : OracleComp FullSpec A) (budget : Budget) (bounded : Budget.Respects (mode:=.O) budget work) :
    work.IsQueryBoundP Sending budget.sends := by
  have last := union_bound (fun query=>queryClass query=12) (fun query=>queryClass query=13) work _ _ (bounded 12) (bounded 13)
  have rest := union_bound (fun query=>queryClass query=10) (fun query=>queryClass query=12 ∨queryClass query=13) work _ _ (bounded 10) last
  have all := union_bound (fun query=>queryClass query=8) (fun query=>queryClass query=10 ∨queryClass query=12 ∨queryClass query=13) work _ _ (bounded 8) rest
  apply (isQueryBoundP_congr_pred (p:=fun query=>queryClass query=8 ∨queryClass query=10 ∨queryClass query=12 ∨queryClass query=13) (p':=Sending) (fun _=>Iff.rfl)).mp
  simpa [Budget.cap,Budget.sends,Nat.add_assoc] using all

/-- The actual native entropy compiler and observation wrapper preserve the exact original all-attempt sending allowance. -/
theorem compiled (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (budget : Budget) (bounded : RegistrationNativeInterface.Respects budget work) :
    (PqxdhDeploymentInterface.asModeO mode (RegistrationNativeEntropyCompile.compile mode work)).IsQueryBoundP Sending budget.sends := by
  have transported := RegistrationNativeEntropyBounds.compile_respects mode work budget bounded
  have observed :=PqxdhDeploymentCompileSecrecy.asModeO_bound mode (RegistrationNativeEntropyCompile.compile mode work)
    (RegistrationNativeEntropyBounds.budget budget) transported
  have old := bound _ (RegistrationNativeEntropyBounds.budget budget) observed
  simpa only [RegistrationNativeEntropyBounds.budget,Budget.sends] using old
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendCallbackBudget

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendCallbackBudget.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendCallbackBudget.bound


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendCallbackBudget.compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginSendCallbackBudget.compiled

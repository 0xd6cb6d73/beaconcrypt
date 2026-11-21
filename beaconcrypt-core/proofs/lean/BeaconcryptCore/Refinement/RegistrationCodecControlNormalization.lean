-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterRecordRequestMonad

/-! Control-flow normalization for generated Boolean validators. Leaves retain arbitrary typed effects and their complete state; distributing a tested Boolean continuation through a branch preserves their order and every failure outcome. Source transformation certificates must instantiate this algebra with the actual validator syntax and exact leaf statements. -/
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationCodecControlNormalization
universe v
variable {m : Type → Type v} [Monad m] [LawfulMonad m]
variable {A B Result : Type}

omit [LawfulMonad m] in
theorem bind_branch (condition : Bool) (yes no : m A) (next : A → m B) :
    ((if condition then yes else no) >>= next) =
      (if condition then yes >>= next else no >>= next) := by
  cases condition <;> rfl

inductive Tree (m : Type → Type v) (Result : Type) : Type (max 1 v) where
  | done (result : Result)
  | leaf {A : Type} (work : m A) (next : A → Tree m Result)
  | branch (condition : Bool) (yes no : Tree m Result)

def evaluate : Tree m Result → m Result
  | .done result => pure result
  | .leaf work next => work >>= fun value => evaluate (next value)
  | .branch condition yes no => if condition then evaluate yes else evaluate no

def cps (next : Result → m B) : Tree m Result → m B
  | .done result => next result
  | .leaf work continuation => work >>= fun value => cps next (continuation value)
  | .branch condition yes no => if condition then cps next yes else cps next no

theorem cps_preserves (tree : Tree m Result) (next : Result → m B) :
    cps next tree = evaluate tree >>= next := by
  induction tree with
  | done result => simp only [cps, evaluate, pure_bind]
  | leaf work continuation ih => simp only [cps, evaluate, ih, bind_assoc]
  | branch condition yes no yesProof noProof =>
      cases condition <;> simp only [cps, evaluate, Bool.false_eq_true, ite_false, ite_true, yesProof, noProof]

theorem run_preserves (tree : Tree m Result) : cps pure tree = evaluate tree := by
  rw [cps_preserves, bind_pure]

end BeaconcryptCore.Refinement.RegistrationCodecControlNormalization

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecControlNormalization.bind_branch' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecControlNormalization.bind_branch

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecControlNormalization.cps_preserves' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecControlNormalization.cps_preserves

/-- info: 'BeaconcryptCore.Refinement.RegistrationCodecControlNormalization.run_preserves' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationCodecControlNormalization.run_preserves

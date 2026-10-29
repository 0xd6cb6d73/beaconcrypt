-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOptionalSupport

/-! Completed optional native programs preserve a state projection when each of their actual callbacks preserves it. Failures retain their real reached state, but cannot become completed continuations. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOptionalFrame
variable {ι S Value Next Projection : Type} {spec : OracleSpec ι}

def Keeps (view : S → Projection) (implementation : QueryImpl spec (OptionT (StateT S ProbComp)))
    (work : OracleComp spec Value) : Prop :=
  ∀ before after value, (some value, after) ∈ support (((simulateQ implementation work).run).run before) →
    view after = view before

/-- A pure native result preserves the complete selected state projection. -/
theorem pure_keeps (view : S → Projection) (implementation : QueryImpl spec (OptionT (StateT S ProbComp)))
    (value : Value) : Keeps view implementation (pure value) := by
  intro before after result supported
  simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff,
    Prod.mk.injEq] at supported
  rw [supported.2]

/-- Two actual optional native pieces preserve the projection in their original order. -/
theorem bind_keeps (view : S → Projection) (implementation : QueryImpl spec (OptionT (StateT S ProbComp)))
    (work : OracleComp spec Value) (next : Value → OracleComp spec Next)
    (first : Keeps view implementation work) (rest : ∀ value, Keeps view implementation (next value)) :
    Keeps view implementation (work >>= next) := by
  intro before after value supported
  simp only [simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨reply, reached⟩, prefixSupport, tail⟩ := supported
  cases reply with
  | none =>
      simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq,
        reduceCtorEq, false_and] at tail
  | some reply => exact (rest reply reached after value tail).trans (first before reached reply prefixSupport)

/-- The full open controller retains the projection by its actual callback laws, with no terminal-state simulation premise. -/
theorem simulate_keeps {κ : Type} {input : OracleSpec κ} (view : S → Projection)
    (implementation : QueryImpl spec (OptionT (StateT S ProbComp)))
    (callbacks : QueryImpl input (OracleComp spec))
    (preserved : ∀ query, Keeps view implementation (callbacks query)) (work : OracleComp input Value) :
    Keeps view implementation (simulateQ callbacks work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_keeps view implementation value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_keeps view implementation _ _ (preserved query) ih

end BeaconcryptCore.Computational.RegistrationNativeOptionalFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOptionalFrame.pure_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOptionalFrame.pure_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOptionalFrame.bind_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOptionalFrame.bind_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOptionalFrame.simulate_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOptionalFrame.simulate_keeps

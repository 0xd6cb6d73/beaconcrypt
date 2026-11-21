-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCandidateObservation

/-! A completed execution under an optional stateful native provider is supported by its actual open controller syntax. Provider failures cannot invent a completed controller result; all native controller gates remain in place. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOptionalSupport
variable {ι S Value : Type} {spec : OracleSpec ι}

/-- Every completed optional source result comes from an actual supported path of the open native controller. -/
theorem completed_support
    (implementation : QueryImpl spec (OptionT (StateT S ProbComp)))
    (work : OracleComp spec Value) (value : Value) (before after : S)
    (supported : (some value, after) ∈ support (((simulateQ implementation work).run).run before)) :
    value ∈ support work := by
  induction work using OracleComp.inductionOn generalizing before after with
  | pure original =>
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff,
        Prod.mk.injEq, Option.some.injEq] at supported
      rw [supported.1]
      simp only [mem_support_pure_iff]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply, reached⟩, _prefix, tail⟩ := supported
      cases reply with
      | none =>
          simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff,
            Prod.mk.injEq, reduceCtorEq, false_and] at tail
      | some reply =>
          rw [mem_support_bind_iff]
          exact ⟨reply, mem_support_query query reply, ih reply reached after tail⟩

end BeaconcryptCore.Computational.RegistrationNativeOptionalSupport

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOptionalSupport.completed_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOptionalSupport.completed_support

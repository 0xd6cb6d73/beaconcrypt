-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawPreScan
import BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy

/-! Prefix projections through native programs that issue no raw accept. This includes every actual secrecy-generated test/fresh continuation; their coins and established sends cannot cross the selected registration cut. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawAnomalyNoAccept
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentCompileBudget (commandKind)
variable {Source Target Result : Type}

/-- Actual no-accept programs preserve their prefix invariant and exact accept counter while commuting with the proved native state projection. -/
theorem project_run
    (source : QueryImpl Spec (StateT Source ProbComp)) (target : QueryImpl Spec (StateT Target ProbComp))
    (project : Source → Target) (inv : Source → Prop) (counter : Source → Nat)
    (step : ∀ query state, inv state → commandKind query ≠ 3 →
      Prod.map id project <$> (source query).run state = (target query).run (project state))
    (keeps : ∀ query state, inv state → commandKind query ≠ 3 →
      ∀ value ∈ support ((source query).run state), inv value.2 ∧ counter value.2 = counter state)
    (work : OracleComp Spec Result) (bounded : work.IsQueryBoundP (fun query => commandKind query = 3) 0)
    (state : Source) (valid : inv state) :
    Prod.map id project <$> (simulateQ source work).run state = (simulateQ target work).run (project state) ∧
      ∀ value ∈ support ((simulateQ source work).run state), inv value.2 ∧ counter value.2 = counter state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
      refine ⟨by simp, ?_⟩
      intro result reached
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
      subst result
      exact ⟨valid, rfl⟩
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      have free : commandKind query ≠ 3 := by
        intro selected
        exact bounded.1.elim (fun rejected => rejected selected) (Nat.not_lt_zero _)
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      refine ⟨?_, ?_⟩
      · rw [map_bind, ← step query state valid free, bind_map_left]
        apply bind_congr_of_forall_mem_support
        intro result reached
        have held := keeps query state valid free result reached
        exact (ih result.1 (by simpa only [ite_eq_right free, Nat.zero_sub] using bounded.2 result.1)
          result.2 held.1).1
      · intro value reached
        rw [mem_support_bind_iff] at reached
        obtain ⟨result, head, tail⟩ := reached
        have held := keeps query state valid free result head
        have final := (ih result.1 (by simpa only [ite_eq_right free, Nat.zero_sub] using bounded.2 result.1)
          result.2 held.1).2 value tail
        exact ⟨final.1, final.2.trans held.2⟩

/-- Every actual secrecy-generated callback program has zero raw accept attempts, independent of its private draws and optional send result. -/
theorem secrecy_no_accept {Reader Response : Type} (crypto : Pqxdh.Crypto)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (query : PqxdhDeploymentInterface.Secrecy)
    (ledger : PqxdhDeploymentSecrecy.Ledger) :
    ((PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds (.inr query)).run ledger).IsQueryBoundP
      (fun request => commandKind request = 3) 0 := by
  have bounded := PqxdhDeploymentCompileSecrecy.wrap_step crypto codec serverKid bounds 3 (.inr query) ledger
  cases query <;> simpa [PqxdhDeploymentCompileSecrecy.wrapCost,
    PqxdhDeploymentInterface.queryClass] using bounded

end BeaconcryptCore.Computational.CborRawAnomalyNoAccept

/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyNoAccept.project_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyNoAccept.project_run
/-- info: 'BeaconcryptCore.Computational.CborRawAnomalyNoAccept.secrecy_no_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawAnomalyNoAccept.secrecy_no_accept

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawPreSource

/-! A raw-attempt scan transports an actual per-query state projection until the selected accept. The counter advances on every accept attempt, including rejection. The source invariant and the exact pending ordinal are retained on every supported outcome. Concrete raw-source instantiations discharge the step conditions separately. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawScanProjection
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentIdealCut (CutCE scanCE)
open PqxdhDeploymentCompileBudget (commandKind)
variable {Source Target Result : Type}

/-- The exact scanner projection follows from concrete query steps that preserve the source invariant and count original raw accept attempts. -/
theorem scan
    (source : QueryImpl Spec (StateT Source ProbComp)) (target : QueryImpl Spec (StateT Target ProbComp))
    (project : Source → Target) (inv : Source → Prop) (counter : Source → Nat) (selected : Nat)
    (step : ∀ query state, inv state →
      (∀ raw, query = .inr (.accept raw) → counter state ≠ selected) →
      Prod.map id project <$> (source query).run state = (target query).run (project state))
    (keeps : ∀ query state, inv state →
      (∀ raw, query = .inr (.accept raw) → counter state ≠ selected) →
      ∀ value ∈ support ((source query).run state), inv value.2 ∧
        counter value.2 = counter state + if commandKind query = 3 then 1 else 0)
    (work : OracleComp Spec Result) (index : Nat) (state : Source) (valid : inv state)
    (room : counter state + index ≤ selected) :
    Prod.map id project <$> (simulateQ source (scanCE work index)).run state =
        (simulateQ target (scanCE work index)).run (project state) ∧
      ∀ value ∈ support ((simulateQ source (scanCE work index)).run state), inv value.2 ∧
        counter value.2 ≤ counter state + index ∧
        ∀ raw next, value.1 = .pending raw next → counter value.2 = counter state + index := by
  induction work using OracleComp.inductionOn generalizing index state with
  | pure result =>
      rw [PqxdhDeploymentIdealCut.scanCE_pure]
      refine ⟨by simp, ?_⟩
      intro value supported
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨valid, Nat.le_add_right _ _, fun _ _ impossible => by cases impossible⟩
  | query_bind query next ih =>
      have forward (rest : Nat) (counted : index = (if commandKind query = 3 then 1 else 0) + rest)
          (other : ∀ raw, query = .inr (.accept raw) → counter state ≠ selected) :
          Prod.map id project <$>
              (simulateQ source ((Spec.query query : OracleComp Spec _) >>= fun reply => scanCE (next reply) rest)).run
                state =
            (simulateQ target ((Spec.query query : OracleComp Spec _) >>= fun reply => scanCE (next reply) rest)).run
                (project state) ∧
            ∀ value ∈ support ((simulateQ source ((Spec.query query : OracleComp Spec _) >>= fun reply =>
              scanCE (next reply) rest)).run state), inv value.2 ∧ counter value.2 ≤ counter state + index ∧
              ∀ raw continuation, value.1 = .pending raw continuation → counter value.2 = counter state + index := by
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
        refine ⟨?_, ?_⟩
        · rw [map_bind, ← step query state valid other, bind_map_left]
          refine bind_congr_of_forall_mem_support _ fun reached supported => ?_
          obtain ⟨preserved, clock⟩ := keeps query state valid other reached supported
          have roomAfter : counter reached.2 + rest ≤ selected := by omega
          exact (ih reached.1 rest reached.2 preserved roomAfter).1
        · intro value supported
          rw [mem_support_bind_iff] at supported
          obtain ⟨reached, first, supported⟩ := supported
          obtain ⟨preserved, clock⟩ := keeps query state valid other reached first
          have roomAfter : counter reached.2 + rest ≤ selected := by omega
          obtain ⟨final, count, pending⟩ := (ih reached.1 rest reached.2 preserved roomAfter).2 value supported
          exact ⟨final, by omega, fun raw continuation same => by
            have actual := pending raw continuation same
            omega⟩
      by_cases accepts : commandKind query = 3
      · rcases query with coin | command
        · exact absurd accepts (by simp [commandKind])
        · cases command with
          | accept raw =>
              cases index with
              | zero =>
                  rw [PqxdhDeploymentIdealCut.scanCE_accept_zero]
                  refine ⟨by simp, ?_⟩
                  intro value supported
                  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
                  subst supported
                  exact ⟨valid, Nat.le_refl _, fun _ _ _ => rfl⟩
              | succ rest =>
                  rw [PqxdhDeploymentIdealCut.scanCE_accept_succ]
                  exact forward rest (by simp only [commandKind, ite_true]; omega) (fun _ _ => by omega)
          | _ => exact absurd accepts (by simp [commandKind])
      · rw [PqxdhDeploymentIdealCut.scanCE_other query accepts]
        exact forward index (by simp only [accepts, ite_false, Nat.zero_add]) (fun raw same => by
          subst same
          exact absurd rfl accepts)

end BeaconcryptCore.Computational.CborRawScanProjection

/-- info: 'BeaconcryptCore.Computational.CborRawScanProjection.scan' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawScanProjection.scan

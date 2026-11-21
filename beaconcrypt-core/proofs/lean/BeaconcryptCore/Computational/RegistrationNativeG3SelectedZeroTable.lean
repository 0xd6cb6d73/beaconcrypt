-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3SelectedTableRouterRun

/-! The fixed selected table's total zero fallback and the original first-touch sampler coincide on every actual capped key-table program. The original cap excludes overflow internally; no successful native path is replaced by a refusal and no new capacity premise is introduced beyond that original syntactic allowance. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3SelectedZeroTable
open RegistrationNativeG3FirstTouch (Spec Alloc Table take fixed)
open RegistrationNativeG3FirstTouchBound (IsValue)
open PqxdhServerAuthKeySchedule (Output)
variable {n : Nat} {Value : Type}
attribute [local irreducible] uniformSample

def fallback : Output := (List.Vector.replicate 76 0, List.Vector.replicate 32 0)

noncomputable def zero (outputs : Table n) : QueryImpl Spec (StateT (Alloc n) ProbComp)
  | .inl coin => StateT.lift (unifSpec.query coin)
  | .inr point => fun before =>
      let allocated := take point before
      match allocated.1 with
      | some slot => pure (outputs slot, allocated.2)
      | none => pure (fallback, allocated.2)

/-- A current value query within its actual remaining allowance has identical full zero-fallback and total first-touch outcomes. -/
theorem query_source (outputs : Table n) (query : Spec.Domain) (before : Alloc n)
    (room : before.2 + (if IsValue query then 1 else 0) ≤ n) :
    (zero outputs query).run before = (fixed outputs query).run before := by
  cases query with
  | inl coin => rfl
  | inr point =>
      have available : before.2 < n := by
        simp only [IsValue, PqxdhRegistrationJointKemSecondEntry.IsValue, ite_true] at room
        omega
      obtain ⟨slot, someSlot⟩ := RegistrationNativeG3FirstTouch.take_some point before available
      cases allocated : take point before with
      | mk selected after =>
          cases selected with
          | none => simp only [allocated] at someSlot; cases someSlot
          | some slot => simp only [zero, fixed, StateT.run, allocated]

/-- Every complete adaptive key-table client within its original allowance has the exact same full output and allocator state under both total fallback definitions. -/
theorem program_source (outputs : Table n) (work : OracleComp Spec Value) (count : Nat)
    (bounded : work.IsQueryBoundP IsValue count) (before : Alloc n) (room : before.2 + count ≤ n) :
    (simulateQ (zero outputs) work).run before = (simulateQ (fixed outputs) work).run before := by
  induction work using OracleComp.inductionOn generalizing count before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      have affordable : before.2 + (if IsValue query then 1 else 0) ≤ n := by
        split_ifs with counted
        · have positive := bounded.1.resolve_left (not_not.mpr counted)
          omega
        · omega
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [query_source outputs query before affordable]
      apply OracleComp.bind_congr_of_forall_mem_support
      intro result supported
      have grown := RegistrationNativeG3FirstTouchBound.step_progress outputs query before result supported
      have tailRoom : result.2.2 + (if IsValue query then count - 1 else count) ≤ n := by
        split_ifs at grown ⊢ with counted
        · have positive := bounded.1.resolve_left (not_not.mpr counted)
          omega
        · omega
      exact ih result.1 _ (bounded.2 result.1) result.2 tailRoom

end BeaconcryptCore.Computational.RegistrationNativeG3SelectedZeroTable
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SelectedZeroTable.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SelectedZeroTable.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SelectedZeroTable.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SelectedZeroTable.program_source

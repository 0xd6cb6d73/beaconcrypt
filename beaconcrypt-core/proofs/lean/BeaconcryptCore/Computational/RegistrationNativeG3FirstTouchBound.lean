-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3FirstTouch

/-! The original syntactic material-query cap excludes first-touch overflow. A strict allocator retains the same full state and value on every supported bounded execution, so the total fallback sampler is not reachable in the actual capped client. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3FirstTouchBound
open RegistrationNativeG3FirstTouch (Spec Alloc Table take fixed fixed_coin fixed_point)
open PqxdhServerAuthKeySchedule (Output)
variable {n : Nat} {Value : Type}

abbrev IsValue := PqxdhRegistrationJointKemSecondEntry.IsValue (D := Pqxdh.Bytes) (R := Output)

noncomputable def strict (outputs : Table n) : QueryImpl Spec (OptionT (StateT (Alloc n) ProbComp))
  | .inl coin => OptionT.mk fun before =>
      (fun reply => (some reply, before)) <$> (unifSpec.query coin : ProbComp _)
  | .inr point => OptionT.mk fun before =>
      match take point before with
      | (some slot, after) => pure (some (outputs slot), after)
      | (none, after) => pure (none, after)

/-- A capped current request has the same complete strict and total outcome; no refusal is substituted for a native successful path. -/
theorem step_source (outputs : Table n) (query : Spec.Domain) (before : Alloc n)
    (room : before.2 + (if IsValue query then 1 else 0) ≤ n) :
    ((strict outputs query).run).run before =
      (fun result => (some result.1, result.2)) <$> (fixed outputs query).run before := by
  cases query with
  | inl coin =>
      simp only [strict, StateT.run]
      rfl
  | inr point =>
      have available : before.2 < n := by
        simp only [IsValue, PqxdhRegistrationJointKemSecondEntry.IsValue, ite_true] at room
        omega
      obtain ⟨slot, someSlot⟩ := RegistrationNativeG3FirstTouch.take_some point before available
      rw [fixed_point]
      change (match take point before with
        | (some slot, after) => pure (some (outputs slot), after)
        | (none, after) => pure (none, after)) = _
      cases allocated : take point before with
      | mk selected after =>
          cases selected with
          | none => simp only [allocated] at someSlot; cases someSlot
          | some selected => simp only [map_pure]

private theorem point_progress (outputs : Table n) (point : Pqxdh.Bytes) (before : Alloc n)
    (result : Output × Alloc n) (supported : result ∈ support ((fixed outputs (.inr point)).run before)) :
    result.2.2 ≤ before.2 + 1 := by
  have progress := RegistrationNativeG3FirstTouch.take_progress point before
  rw [fixed_point] at supported
  cases allocated : take point before with
  | mk selected after =>
      simp only [allocated] at progress supported
      cases selected with
      | none =>
          rw [support_map] at supported
          obtain ⟨reply, -, same⟩ := supported
          simpa only [← same] using progress
      | some selected =>
          rw [mem_support_pure_iff] at supported
          simpa only [supported] using progress

/-- Total allocator execution spends at most one fresh slot at a value request and zero at an ordinary coin. -/
theorem step_progress (outputs : Table n) (query : Spec.Domain) (before : Alloc n)
    (result : Spec.Range query × Alloc n) (supported : result ∈ support ((fixed outputs query).run before)) :
    result.2.2 ≤ before.2 + (if IsValue query then 1 else 0) := by
  cases query with
  | inl coin =>
      rw [fixed_coin, support_map] at supported
      obtain ⟨reply, _sampled, rfl⟩ := supported
      exact le_rfl
  | inr point => exact point_progress outputs point before result supported

/-- Every adaptive client within its original value-query allowance avoids overflow and keeps the literal full allocator state. -/
theorem program_source (outputs : Table n) (work : OracleComp Spec Value) (count : Nat)
    (bounded : work.IsQueryBoundP IsValue count) (before : Alloc n) (room : before.2 + count ≤ n) :
    (((simulateQ (strict outputs) work).run).run before) =
      (fun result => (some result.1, result.2)) <$> (simulateQ (fixed outputs) work).run before := by
  induction work using OracleComp.inductionOn generalizing count before with
  | pure value => rfl
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      have affordable : before.2 + (if IsValue query then 1 else 0) ≤ n := by
        split_ifs with counted
        · have positive := bounded.1.resolve_left (not_not.mpr counted)
          omega
        · omega
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind, map_bind]
      rw [step_source outputs query before affordable, bind_map_left]
      apply OracleComp.bind_congr_of_forall_mem_support
      intro result supported
      simp only [Option.elim_some]
      have grown := step_progress outputs query before result supported
      have tailRoom : result.2.2 + (if IsValue query then count - 1 else count) ≤ n := by
        split_ifs at grown ⊢ with counted
        · have positive := bounded.1.resolve_left (not_not.mpr counted)
          omega
        · omega
      exact ih result.1 _ (bounded.2 result.1) result.2 tailRoom

/-- Starting with the genuine empty allocator, a client of at most n material requests cannot reach overflow. -/
theorem no_overflow (outputs : Table n) (work : OracleComp Spec Value) (bounded : work.IsQueryBoundP IsValue n) :
    (((simulateQ (strict outputs) work).run).run PqxdhRegistrationJointKemSecondEntry.emptyAlloc) =
      (fun result => (some result.1, result.2)) <$>
        (simulateQ (fixed outputs) work).run PqxdhRegistrationJointKemSecondEntry.emptyAlloc :=
  program_source outputs work n bounded _ (by simp [PqxdhRegistrationJointKemSecondEntry.emptyAlloc])

end BeaconcryptCore.Computational.RegistrationNativeG3FirstTouchBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3FirstTouchBound.step_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3FirstTouchBound.step_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3FirstTouchBound.step_progress' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3FirstTouchBound.step_progress
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3FirstTouchBound.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3FirstTouchBound.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3FirstTouchBound.no_overflow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3FirstTouchBound.no_overflow

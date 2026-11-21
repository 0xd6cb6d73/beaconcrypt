-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaFiniteMonitor

/-! A source-derived finite cover charges the union of bad cuts and final cache collision only once. The operational extension condition concerns the actual shared state, and every generation allowance and adaptive continuation remains in the original query-bound induction. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaFiniteFinal
open RegistrationNativeMldsaStop (Observer)
open RegistrationNativeMldsaFiniteMonitor (State advance handler coordinate_program)
variable {S Index Candidate V I : Type} {spec : OracleSpec I}
private theorem bind_apply {m : Type → Type} [Monad m] {S A B : Type}
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let middle ← work before; next middle.1 middle.2) := rfl

private def Good (safe : S → Prop) (collision : S → Prop) (before : State S Index Candidate) : Prop :=
  safe before.native ∧ (before.bad = true → collision before.native ∨ ∃ index, (before.selected index).isSome = true)

private theorem orElse_kept (old added : Option Candidate) (someOld : old.isSome = true) :
    (old.orElse fun _ => added).isSome = true := by
  cases old with
  | none => cases someOld
  | some value => rfl

private theorem orElse_added (old added : Option Candidate) (someAdded : added.isSome = true) :
    (old.orElse fun _ => added).isSome = true := by
  cases old with
  | none => exact someAdded
  | some value => rfl

private theorem advance_good
    (bad : (query : spec.Domain) → S → spec.Range query → S → Prop) (collision : S → Prop)
    (observe : Index → Observer (spec := spec) (State := S) (Candidate := Candidate))
    (safe : S → Prop) (query : spec.Domain) (before : State S Index Candidate) (reply : spec.Range query) (after : S)
    (previous : Good safe collision before) (safeAfter : safe after)
    (extended : collision before.native → collision after)
    (covered : bad query before.native reply after → collision after ∨ ∃ index, (observe index query before.native reply after).isSome = true) :
    Good safe collision (advance bad collision observe query before reply after) := by
  classical
  refine ⟨safeAfter, ?_⟩
  intro selected
  change before.bad || decide (bad query before.native reply after) = true at selected
  rcases Bool.or_eq_true_iff.mp selected with old | fresh
  · rcases previous.2 old with collided | ⟨index, captured⟩
    · exact Or.inl (extended collided)
    · exact Or.inr ⟨index, orElse_kept _ _ captured⟩
  · rcases covered (of_decide_eq_true fresh) with collided | ⟨index, captured⟩
    · exact Or.inl collided
    · exact Or.inr ⟨index, orElse_added _ _ captured⟩

private theorem program_good (source : QueryImpl spec (StateT S ProbComp))
    (bad : (query : spec.Domain) → S → spec.Range query → S → Prop) (collision : S → Prop)
    (observe : Index → Observer (spec := spec) (State := S) (Candidate := Candidate))
    (safe : S → Prop) (counter : S → Nat) (cost : spec.Domain → Prop) [DecidablePred cost] (cap : Nat)
    (preserves : ∀ query before result, safe before → result ∈ support ((source query).run before) → safe result.2)
    (grows : ∀ query before result, safe before → result ∈ support ((source query).run before) →
      counter result.2 ≤ counter before + (if cost query then 1 else 0))
    (extendsCollision : ∀ query before result, safe before → result ∈ support ((source query).run before) → collision before → collision result.2)
    (covers : ∀ query before result, safe before → counter before ≤ cap → result ∈ support ((source query).run before) →
      bad query before result.1 result.2 → collision result.2 ∨ ∃ index, (observe index query before result.1 result.2).isSome = true)
    (work : OracleComp spec V) (remaining : Nat) (bounded : work.IsQueryBoundP cost remaining)
    (before : State S Index Candidate) (previous : Good safe collision before) (room : counter before.native + remaining ≤ cap)
    (result : V × State S Index Candidate)
    (supported : result ∈ support ((simulateQ (handler source bad collision observe) work).run before)) : Good safe collision result.2 := by
  induction work using OracleComp.inductionOn generalizing before remaining with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact previous
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query, bind_apply, handler, StateT.run,
        mem_support_bind_iff, support_map] at supported
      obtain ⟨middle, ⟨raw, reached, same⟩, continued⟩ := supported
      cases same
      have advanced : Good safe collision (advance bad collision observe query before raw.1 raw.2) :=
        advance_good bad collision observe safe query before raw.1 raw.2 previous
          (preserves query before.native raw previous.1 reached)
          (extendsCollision query before.native raw previous.1 reached)
          (covers query before.native raw previous.1 (by omega) reached)
      have count := grows query before.native raw previous.1 reached
      have ceiling : counter raw.2 + (if cost query then remaining - 1 else remaining) ≤ cap := by
        by_cases charged : cost query
        · have positive : 0 < remaining := bounded.1.resolve_left (fun negative => negative charged)
          simp only [charged, ite_true] at count ⊢
          omega
        · simp only [charged, ite_false] at count ⊢
          omega
      exact ih raw.1 _ (bounded.2 raw.1) _ advanced ceiling continued

/-- The actual bad-cut/final-collision union is bounded by one final collision mass and the unchanged finite coordinate monitors. -/
theorem bound [Fintype Index] (source : QueryImpl spec (StateT S ProbComp))
    (bad : (query : spec.Domain) → S → spec.Range query → S → Prop) (collision : S → Prop)
    (observe : Index → Observer (spec := spec) (State := S) (Candidate := Candidate))
    (safe : S → Prop) (counter : S → Nat) (cost : spec.Domain → Prop) [DecidablePred cost] (cap : Nat)
    (preserves : ∀ query before result, safe before → result ∈ support ((source query).run before) → safe result.2)
    (grows : ∀ query before result, safe before → result ∈ support ((source query).run before) →
      counter result.2 ≤ counter before + (if cost query then 1 else 0))
    (extendsCollision : ∀ query before result, safe before → result ∈ support ((source query).run before) → collision before → collision result.2)
    (covers : ∀ query before result, safe before → counter before ≤ cap → result ∈ support ((source query).run before) →
      bad query before result.1 result.2 → collision result.2 ∨ ∃ index, (observe index query before result.1 result.2).isSome = true)
    (work : OracleComp spec V) (remaining : Nat) (bounded : work.IsQueryBoundP cost remaining)
    (before : S) (initial : safe before) (room : counter before + remaining ≤ cap) :
    Pr{let result ← (simulateQ (handler source bad collision observe) work).run ({ native := before } : State S Index Candidate)}[result.2.bad = true ∨ collision result.2.native] ≤
      Pr{let result ← (simulateQ (handler source bad collision observe) work).run ({ native := before } : State S Index Candidate)}[collision result.2.native] +
        ∑ index, Pr{let result ← (simulateQ (RegistrationNativeMldsaStop.monitor source (observe index)) work).run (before, none)}[
          result.2.2.isSome = true] := by
  classical
  let joint := (simulateQ (handler source bad collision observe) work).run ({ native := before } : State S Index Candidate)
  have covered : ∀ result ∈ support joint, result.2.bad = true ∨ collision result.2.native →
      collision result.2.native ∨ ∃ index, (result.2.selected index).isSome = true := by
    intro result supported selected
    rcases selected with selected | collided
    · exact (program_good source bad collision observe safe counter cost cap preserves grows extendsCollision covers work remaining bounded
        ({ native := before } : State S Index Candidate) ⟨initial, by intro impossible; cases impossible⟩ room result supported).2 selected
    · exact Or.inl collided
  have union := prEvent_exists_le joint (fun index result => (result.2.selected index).isSome = true)
  have coordinates : (∑ index, Pr{let result ← joint}[(result.2.selected index).isSome = true]) =
      ∑ index, Pr{let result ← (simulateQ (RegistrationNativeMldsaStop.monitor source (observe index)) work).run (before, none)}[
          result.2.2.isSome = true] := by
    apply Finset.sum_congr rfl
    intro index _member
    rw [← coordinate_program source bad collision observe index work ({ native := before } : State S Index Candidate), prEvent_map]
    rfl
  exact (prEvent_mono_of_support joint _ _ covered).trans
    ((prEvent_or_le joint _ _).trans (add_le_add le_rfl (coordinates ▸ union)))

end BeaconcryptCore.Computational.RegistrationNativeMldsaFiniteFinal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaFiniteFinal.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaFiniteFinal.bound

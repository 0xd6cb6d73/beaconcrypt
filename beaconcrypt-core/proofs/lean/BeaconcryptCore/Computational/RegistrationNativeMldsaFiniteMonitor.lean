-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaMonitorOrder

/-! A finite family of observers monitors one complete adaptive source execution. Its coordinate laws and finite union bound use no independence. A structural query budget retains the source counter ceiling at every cut. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaFiniteMonitor
open RegistrationNativeMldsaStop (Observer)
variable {Query S Index Candidate V : Type} {spec : OracleSpec Query}

structure State (S Index Candidate : Type) where
  native : S
  bad : Bool := false
  collision : Bool := false
  selected : Index → Option Candidate := fun _ => none

noncomputable def advance (bad : (query : spec.Domain) → S → spec.Range query → S → Prop)
    (collision : S → Prop) (observe : Index → Observer (spec := spec) (State := S) (Candidate := Candidate))
    (query : spec.Domain) (before : State S Index Candidate) (reply : spec.Range query) (after : S) : State S Index Candidate := by
  classical
  exact ⟨after, before.bad || decide (bad query before.native reply after), before.collision || decide (collision after),
    fun index => (before.selected index).orElse fun _ => observe index query before.native reply after⟩

noncomputable def handler (source : QueryImpl spec (StateT S ProbComp))
    (bad : (query : spec.Domain) → S → spec.Range query → S → Prop) (collision : S → Prop)
    (observe : Index → Observer (spec := spec) (State := S) (Candidate := Candidate)) :
    QueryImpl spec (StateT (State S Index Candidate) ProbComp) := fun query before =>
  (fun result => (result.1, advance bad collision observe query before result.1 result.2)) <$> (source query).run before.native

def coordinate (index : Index) (result : V × State S Index Candidate) : V × (S × Option Candidate) :=
  (result.1, (result.2.native, result.2.selected index))

private theorem bind_apply {m : Type → Type} [Monad m] {T A B : Type}
    (work : StateT T m A) (next : A → StateT T m B) (before : T) :
    (work >>= next) before = (do let middle ← work before; next middle.1 middle.2) := rfl

/-- Every family coordinate is exactly its standalone full first-candidate monitor on the same native source execution. -/
theorem coordinate_program (source : QueryImpl spec (StateT S ProbComp))
    (bad : (query : spec.Domain) → S → spec.Range query → S → Prop) (collision : S → Prop)
    (observe : Index → Observer (spec := spec) (State := S) (Candidate := Candidate))
    (index : Index) (work : OracleComp spec V) (before : State S Index Candidate) :
    coordinate index <$> (simulateQ (handler source bad collision observe) work).run before =
      (simulateQ (RegistrationNativeMldsaStop.monitor source (observe index)) work).run (before.native, before.selected index) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, coordinate]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, bind_apply, handler,
        RegistrationNativeMldsaStop.monitor, StateT.run, map_bind, bind_map_left, bind_assoc, pure_bind]
      apply bind_congr
      intro middle
      exact ih middle.1 _

/-- The family retains the original adaptive source execution after erasing its analysis flags. -/
theorem erase (source : QueryImpl spec (StateT S ProbComp))
    (bad : (query : spec.Domain) → S → spec.Range query → S → Prop) (collision : S → Prop)
    (observe : Index → Observer (spec := spec) (State := S) (Candidate := Candidate))
    (work : OracleComp spec V) (before : State S Index Candidate) :
    (fun result => (result.1, result.2.native)) <$> (simulateQ (handler source bad collision observe) work).run before =
      (simulateQ source work).run before.native := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, bind_apply, handler, StateT.run, map_bind, bind_map_left]
      apply bind_congr
      intro middle
      exact ih middle.1 _

private def Good (safe : S → Prop) (before : State S Index Candidate) : Prop :=
  safe before.native ∧ (before.bad = true → before.collision = true ∨ ∃ index, (before.selected index).isSome = true)

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
    (previous : Good safe before) (safeAfter : safe after)
    (covered : bad query before.native reply after → collision after ∨ ∃ index, (observe index query before.native reply after).isSome = true) :
    Good safe (advance bad collision observe query before reply after) := by
  classical
  refine ⟨safeAfter, ?_⟩
  intro selected
  change before.bad || decide (bad query before.native reply after) = true at selected
  rcases Bool.or_eq_true_iff.mp selected with old | fresh
  · rcases previous.2 old with collided | ⟨index, captured⟩
    · exact Or.inl (by simp only [advance, collided, Bool.true_or])
    · exact Or.inr ⟨index, orElse_kept _ _ captured⟩
  · rcases covered (of_decide_eq_true fresh) with collided | ⟨index, captured⟩
    · exact Or.inl (by simp only [advance, collided, decide_true, Bool.or_true])
    · exact Or.inr ⟨index, orElse_added _ _ captured⟩

private theorem program_good (source : QueryImpl spec (StateT S ProbComp))
    (bad : (query : spec.Domain) → S → spec.Range query → S → Prop) (collision : S → Prop)
    (observe : Index → Observer (spec := spec) (State := S) (Candidate := Candidate))
    (safe : S → Prop) (counter : S → Nat) (cost : spec.Domain → Prop) [DecidablePred cost] (cap : Nat)
    (preserves : ∀ query before result, safe before → result ∈ support ((source query).run before) → safe result.2)
    (grows : ∀ query before result, safe before → result ∈ support ((source query).run before) →
      counter result.2 ≤ counter before + (if cost query then 1 else 0))
    (covers : ∀ query before result, safe before → counter before ≤ cap → result ∈ support ((source query).run before) →
      bad query before result.1 result.2 → collision result.2 ∨ ∃ index, (observe index query before result.1 result.2).isSome = true)
    (work : OracleComp spec V) (remaining : Nat) (bounded : work.IsQueryBoundP cost remaining)
    (before : State S Index Candidate) (previous : Good safe before) (room : counter before.native + remaining ≤ cap)
    (result : V × State S Index Candidate)
    (supported : result ∈ support ((simulateQ (handler source bad collision observe) work).run before)) : Good safe result.2 := by
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
      have advanced : Good safe (advance bad collision observe query before raw.1 raw.2) :=
        advance_good bad collision observe safe query before raw.1 raw.2 previous
          (preserves query before.native raw previous.1 reached)
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

/-- The original bad-cut marker is bounded by the same-run sticky collision marker and the finite sum of unchanged coordinate monitors. Only actual source-step and query-budget facts are used. -/
theorem bound [Fintype Index] (source : QueryImpl spec (StateT S ProbComp))
    (bad : (query : spec.Domain) → S → spec.Range query → S → Prop) (collision : S → Prop)
    (observe : Index → Observer (spec := spec) (State := S) (Candidate := Candidate))
    (safe : S → Prop) (counter : S → Nat) (cost : spec.Domain → Prop) [DecidablePred cost] (cap : Nat)
    (preserves : ∀ query before result, safe before → result ∈ support ((source query).run before) → safe result.2)
    (grows : ∀ query before result, safe before → result ∈ support ((source query).run before) →
      counter result.2 ≤ counter before + (if cost query then 1 else 0))
    (covers : ∀ query before result, safe before → counter before ≤ cap → result ∈ support ((source query).run before) →
      bad query before result.1 result.2 → collision result.2 ∨ ∃ index, (observe index query before result.1 result.2).isSome = true)
    (work : OracleComp spec V) (remaining : Nat) (bounded : work.IsQueryBoundP cost remaining)
    (before : S) (initial : safe before) (room : counter before + remaining ≤ cap) :
    Pr{let result ← (simulateQ (handler source bad collision observe) work).run ({ native := before } : State S Index Candidate)}[result.2.bad = true] ≤
      Pr{let result ← (simulateQ (handler source bad collision observe) work).run ({ native := before } : State S Index Candidate)}[result.2.collision = true] +
        ∑ index, Pr{let result ← (simulateQ (RegistrationNativeMldsaStop.monitor source (observe index)) work).run (before, none)}[
          result.2.2.isSome = true] := by
  classical
  let joint := (simulateQ (handler source bad collision observe) work).run ({ native := before } : State S Index Candidate)
  have covered : ∀ result ∈ support joint, result.2.bad = true →
      result.2.collision = true ∨ ∃ index, (result.2.selected index).isSome = true := by
    intro result supported
    exact (program_good source bad collision observe safe counter cost cap preserves grows covers work remaining bounded
      ({ native := before } : State S Index Candidate) ⟨initial, by intro impossible; cases impossible⟩ room result supported).2
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

end BeaconcryptCore.Computational.RegistrationNativeMldsaFiniteMonitor
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaFiniteMonitor.coordinate_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaFiniteMonitor.coordinate_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaFiniteMonitor.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaFiniteMonitor.erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaFiniteMonitor.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaFiniteMonitor.bound

-- SPDX-License-Identifier: 0BSD
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic

/-!
# Persistent lazy uniform tables

This generic component records both table lookups and fresh uniform samples. The table is independent of a caller's transactional state: rolling the caller back does not roll the table back. It does not identify any concrete function with a random table.
-/

open OracleComp OracleSpec

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
  [∀ t : spec.Domain, SampleableType (spec.Range t)]

/-- Counts logical table lookups and fresh uniform sampling operations, not sampler bit cost. -/
structure Counts where
  lookups : Nat
  draws : Nat
  deriving DecidableEq

/-- Cached values and their accounting live outside the caller's transactional state. -/
abbrev State (spec : OracleSpec ι) := spec.QueryCache × Counts

/-- Empty table with no lookups or fresh draws. -/
def initial : State spec := (∅, ⟨0, 0⟩)

/-- The auxiliary update on a hit charges one lookup and no fresh draw. -/
def hit (t : spec.Domain) (_ : spec.Range t) (_ : spec.QueryCache) (c : Counts) : Counts :=
  ⟨c.lookups + 1, c.draws⟩

/-- The miss branch samples a uniform answer and charges exactly one fresh draw. -/
noncomputable def miss (t : spec.Domain) (_ : spec.QueryCache) (c : Counts) :
    ProbComp (spec.Range t × Counts) :=
  (fun answer => (answer, ⟨c.lookups + 1, c.draws + 1⟩)) <$> ($ᵗ spec.Range t)

/-- VCVio's lazy cache, with accounting for each hit or miss. -/
noncomputable def impl : QueryImpl spec (StateT (State spec) ProbComp) :=
  QueryImpl.withCachingAux hit miss

/-- A miss exposes exactly one uniform answer and its updated complete table state. -/
theorem run_miss (t : spec.Domain) (s : State spec) (h : s.1 t = none) :
    (impl t).run s =
      (fun answer => (answer, (s.1.cacheQuery t answer,
        ⟨s.2.lookups + 1, s.2.draws + 1⟩))) <$> ($ᵗ spec.Range t) := by
  simp [impl, QueryImpl.withCachingAux_apply, h, miss, Functor.map_map]

/-- A hit preserves every cached value and charges no uniform sample. -/
theorem run_hit (t : spec.Domain) (s : State spec) (answer : spec.Range t)
    (h : s.1 t = some answer) :
    (impl t).run s = pure (answer, (s.1, ⟨s.2.lookups + 1, s.2.draws⟩)) := by
  simp [impl, QueryImpl.withCachingAux_apply, h, hit]

/-- The fresh-draw law holds for any continuation of the answer and the complete updated state. -/
theorem miss_continuation {α : Type} (t : spec.Domain) (s : State spec)
    (h : s.1 t = none) (continuation : spec.Range t × State spec → ProbComp α) :
    ((impl t).run s >>= continuation) =
      (($ᵗ spec.Range t) >>= fun answer =>
        continuation (answer, (s.1.cacheQuery t answer,
          ⟨s.2.lookups + 1, s.2.draws + 1⟩))) := by
  rw [run_miss t s h, bind_map_left]

/-- Whether a logical lookup needs one fresh sample. -/
def freshCost (cache : spec.QueryCache) (t : spec.Domain) : Nat :=
  if (cache t).isSome then 0 else 1

/-- Every possible single-query outcome records the answer, keeps earlier answers, and has exact costs. -/
theorem step_facts (t : spec.Domain) (s : State spec)
    (z : spec.Range t × State spec) (hz : z ∈ support ((impl t).run s)) :
    z.2.1 t = some z.1 ∧ s.1 ≤ z.2.1 ∧
      z.2.2.lookups = s.2.lookups + 1 ∧
      z.2.2.draws = s.2.draws + freshCost s.1 t := by
  cases hc : s.1 t with
  | some answer =>
      simp only [run_hit t s answer hc, support_pure, Set.mem_singleton_iff] at hz
      subst z
      simp [hc, freshCost]
  | none =>
      simp only [run_miss t s hc, support_map] at hz
      obtain ⟨answer, _, rfl⟩ := hz
      exact ⟨QueryCache.cacheQuery_self _ _ _, QueryCache.le_cacheQuery _ hc,
        rfl, by simp [freshCost, hc]⟩

/-- Discarding only the counters gives VCVio's lazy uniform oracle, including its complete cache. -/
theorem run_project {α : Type} (program : OracleComp spec α) (s : State spec) :
    Prod.map id Prod.fst <$> (simulateQ impl program).run s =
      (simulateQ spec.randomOracle program).run s.1 := by
  exact QueryImpl.withCachingAux_run_proj_eq uniformSampleImpl hit miss
    (by intro t cache counts; simp [miss, uniformSampleImpl_apply, Functor.map_map])
    program s.1 s.2

/-- Any adaptive continuation only extends the persistent table. -/
theorem run_cache_mono {α : Type} (program : OracleComp spec α) (s : State spec)
    (z : α × State spec) (hz : z ∈ support ((simulateQ impl program).run s)) :
    s.1 ≤ z.2.1 :=
  simulateQ_run_preservesInv impl (fun current => s.1 ≤ current.1)
    (fun t current before result hr => before.trans (step_facts t current result hr).2.1)
    program s (le_refl _) z hz

/-- Once an answer was cached, any adaptive table continuation preserves it. -/
theorem run_retains {α : Type} (program : OracleComp spec α) (s : State spec)
    (z : α × State spec) (hz : z ∈ support ((simulateQ impl program).run s))
    (t : spec.Domain) (answer : spec.Range t) (hc : s.1 t = some answer) :
    z.2.1 t = some answer :=
  run_cache_mono program s z hz hc

/-- A caller may restore its own entry state while keeping all table effects of a failed operation. -/
def restoreCaller {Caller : Type} (saved : Caller) (current : Caller × State spec) :
    Caller × State spec := (saved, current.2)

/-- Lift a table query without giving it access to the caller's private state. -/
noncomputable def withCaller {Caller : Type} (t : spec.Domain) :
    StateT (Caller × State spec) ProbComp (spec.Range t) := fun current =>
  (fun z => (z.1, (current.1, z.2))) <$> (impl t).run current.2

/-- Re-querying a cached coordinate after caller rollback returns the same answer with no fresh draw. -/
theorem rollback_hit {Caller : Type} (saved : Caller) (current : Caller × State spec)
    (t : spec.Domain) (answer : spec.Range t) (hc : current.2.1 t = some answer) :
    (withCaller t).run (restoreCaller saved current) =
      pure (answer, (saved, (current.2.1,
        ⟨current.2.2.lookups + 1, current.2.2.draws⟩))) := by
  change (fun z => (z.1, (saved, z.2))) <$> (impl t).run current.2 = _
  rw [run_hit t current.2 answer hc, map_pure]

/-- The first sampled answer survives arbitrary adaptive table work followed by caller rollback. -/
theorem rollback_after_adaptive {Caller α : Type} (saved current : Caller)
    (t : spec.Domain) (s : State spec) (first : spec.Range t × State spec)
    (hfirst : first ∈ support ((impl t).run s)) (program : OracleComp spec α)
    (last : α × State spec)
    (hlast : last ∈ support ((simulateQ impl program).run first.2)) :
    (withCaller t).run (restoreCaller saved (current, last.2)) =
      pure (first.1, (saved, (last.2.1,
        ⟨last.2.2.lookups + 1, last.2.2.draws⟩))) :=
  rollback_hit saved (current, last.2) t first.1
    (run_retains program first.2 last hlast t first.1 (step_facts t s first hfirst).1)

/-- Fresh sampling increases no faster than logical lookups, also from a nonempty initial cache. -/
theorem run_draws_le_lookups {α : Type} (program : OracleComp spec α) (s : State spec)
    (z : α × State spec) (hz : z ∈ support ((simulateQ impl program).run s)) :
    z.2.2.draws + s.2.lookups ≤ s.2.draws + z.2.2.lookups := by
  refine simulateQ_run_preservesInv impl
    (fun current => current.2.draws + s.2.lookups ≤ s.2.draws + current.2.lookups)
    ?_ program s (le_refl _) z hz
  intro t current hc result hr
  have step := step_facts t current result hr
  unfold freshCost at step
  split at step <;> omega

/-- A structural bound on adaptive table queries bounds both additional lookup and fresh-draw counts. -/
theorem run_budget {α : Type} (program : OracleComp spec α) (q : Nat)
    (hb : program.IsTotalQueryBound q) (s : State spec) (z : α × State spec)
    (hz : z ∈ support ((simulateQ impl program).run s)) :
    z.2.2.lookups ≤ s.2.lookups + q ∧ z.2.2.draws ≤ s.2.draws + q := by
  induction program using OracleComp.inductionOn generalizing q s with
  | pure answer => simp_all
  | query_bind t next ih =>
      change z ∈ support ((impl t).run s >>= fun middle =>
        (simulateQ impl (next middle.1)).run middle.2) at hz
      obtain ⟨middle, hm, ht⟩ := (mem_support_bind_iff _ _ _).1 hz
      rw [isTotalQueryBound_query_bind_iff] at hb
      have tail := ih middle.1 (q - 1) (hb.2 middle.1) middle.2 ht
      have step := step_facts t s middle hm
      unfold freshCost at step
      split at step <;> omega

end BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable

/--
info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable.run_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable.run_miss
/--
info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable.run_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable.run_hit
/--
info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable.miss_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable.miss_continuation
/--
info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable.step_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable.step_facts
/--
info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable.run_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable.run_project
/--
info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable.run_cache_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable.run_cache_mono
/--
info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable.run_retains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable.run_retains
/--
info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable.rollback_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable.rollback_hit
/--
info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable.rollback_after_adaptive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable.rollback_after_adaptive
/--
info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable.run_draws_le_lookups' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable.run_draws_le_lookups
/--
info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable.run_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable.run_budget

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsCollision
import BeaconcryptCore.Computational.LazyOracleDiscard

/-! Exact lazy-oracle instrumentation for the two-class digest collision experiment. -/
open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordFactsCollisionOracle
open PqxdhRecordFactsCollision
variable {Input Digest : Type} [DecidableEq Input] [DecidableEq Digest]
  [SampleableType Digest]

abbrev HashSpec (Input Digest : Type) := Input →ₒ Digest
abbrev Cache (Input Digest : Type) := (HashSpec Input Digest).QueryCache
abbrev Spec (Input Digest : Type) := HashSpec Input Digest + unifSpec

/-- The class is determined by the queried input before its missing value is sampled. -/
noncomputable def compiler (target : Input → Bool) :
    QueryImpl (Spec Input Digest) (StateT (Cache Input Digest) (OracleComp (DrawSpec Digest)))
  | .inl input => fun cache =>
      match cache input with
      | some digest => pure (digest, cache)
      | none => do
          let digest ← (DrawSpec Digest).query (.inl (target input))
          pure (digest, cache.cacheQuery input digest)
  | .inr coin => fun cache => do
      let reply ← (DrawSpec Digest).query (.inr coin)
      pure (reply, cache)

/-- The original lazy uniform oracle with arbitrary interleaved finite coins. -/
noncomputable def plain : QueryImpl (Spec Input Digest) (StateT (Cache Input Digest) ProbComp)
  | .inl input => (HashSpec Input Digest).randomOracle input
  | .inr coin => fun cache => (fun reply => (reply, cache)) <$> unifSpec.query coin

/-- The same lazy oracle, with every actual miss entered in the collision history. -/
noncomputable def instrumented (target : Input → Bool) :
    QueryImpl (Spec Input Digest) (StateT (Cache Input Digest × History Digest) ProbComp)
  | .inl input => fun state =>
      match state.1 input with
      | some digest => pure (digest, state)
      | none => do
          let digest ← $ᵗ Digest
          pure (digest, state.1.cacheQuery input digest, state.2.insert (target input) digest)
  | .inr coin => fun state => (fun reply => (reply, state)) <$> unifSpec.query coin

/-- Forgetting the ghost collision history preserves the complete reply and real cache at one query. -/
theorem query_project (target : Input → Bool) (q : (Spec Input Digest).Domain)
    (state : Cache Input Digest × History Digest) :
    Prod.map id Prod.fst <$> (instrumented target q).run state =
      (plain q).run state.1 := by
  cases q with
  | inl input =>
      simp only [instrumented, plain]
      rw [randomOracle.run_eq]
      cases hit : state.1 input <;> simp [StateT.run, hit, Functor.map_map]
  | inr coin => simp only [instrumented, plain, StateT.run, Functor.map_map]; rfl

/-- The entire adaptive client result and cache are identical after forgetting only the ghost history. -/
theorem program_project (target : Input → Bool) {X : Type} (client : OracleComp (Spec Input Digest) X)
    (state : Cache Input Digest × History Digest) :
    Prod.map id Prod.fst <$> (simulateQ (instrumented target) client).run state =
      (simulateQ plain client).run state.1 :=
  map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst (query_project target) client state

/-- Reassociate the real cache and the statistical ghost state without deleting either. -/
def flatten {X : Type} (result : (X × Cache Input Digest) × History Digest) :
    X × (Cache Input Digest × History Digest) := (result.1.1, result.1.2, result.2)

private theorem map_apply {S X Y : Type} (f : X → Y) (work : StateT S ProbComp X)
    (state : S) : (f <$> work) state = Prod.map f id <$> work state := by
  change (work state >>= fun r => pure (f r.1, r.2)) = _
  simp only [bind_pure_comp]; rfl

private theorem pure_apply {S X : Type} (value : X) (state : S) :
    (pure value : StateT S ProbComp X) state = pure (value, state) := rfl

/-- The lazy-oracle compiler uses exactly the reviewed draw experiment on each miss. -/
theorem query_compile (target : Input → Bool) (q : (Spec Input Digest).Domain)
    (state : Cache Input Digest × History Digest) :
    flatten <$> (simulateQ interpreter ((compiler target q).run state.1)).run state.2 =
      (instrumented target q).run state := by
  cases q with
  | inl input =>
      simp only [compiler, instrumented, StateT.run]
      cases hit : state.1 input <;>
        simp [interpreter, map_apply, pure_apply, flatten, Functor.map_map]
  | inr coin =>
      simp [compiler, instrumented, interpreter, StateT.run, map_apply, flatten, Functor.map_map]

/-- The flattened compiler is exactly the instrumented lazy oracle. -/
theorem interpreter_compile (target : Input → Bool) :
    ((interpreter (α := Digest)).mapStateTBase (compiler target)).flattenStateT = instrumented target := by
  ext q state
  exact query_compile target q state

/-- Compilation preserves the full adaptive result, cache and chronological collision ledger. -/
theorem program_compile (target : Input → Bool) {X : Type} (client : OracleComp (Spec Input Digest) X)
    (state : Cache Input Digest × History Digest) :
    flatten <$> (simulateQ interpreter ((simulateQ (compiler target) client).run state.1)).run state.2 =
      (simulateQ (instrumented target) client).run state := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT, interpreter_compile]
  simp only [Functor.map_map, flatten, Prod.eta]
  exact id_map _

omit [DecidableEq Digest] [SampleableType Digest] in
/-- Increasing either class cap preserves the all-reply bound, including arbitrary intervening coins. -/
theorem draw_budget_mono {X : Type} (client : OracleComp (DrawSpec Digest) X)
    (before after : Nat × Nat) (increase : before.1 ≤ after.1 ∧ before.2 ≤ after.2)
    (bounded : client.IsQueryBound before enabled debit) :
    client.IsQueryBound after enabled debit := by
  induction client using OracleComp.inductionOn generalizing before after with
  | pure value => exact isQueryBound_pure _ _ _ _
  | query_bind q next ih =>
      rw [isQueryBound_query_bind_iff] at bounded ⊢
      constructor
      · cases q with
        | inl target => cases target <;> simp only [enabled] at bounded ⊢ <;> omega
        | inr coin => trivial
      · intro reply
        apply ih reply _ _ ?_ (bounded.2 reply)
        cases q with
        | inl target => cases target <;> simp only [debit] <;> omega
        | inr coin => exact increase

/-- Classify a literal lazy-oracle request without inspecting its eventual reply. -/
def drawClass (target : Input → Bool) : Input ⊕ unifSpec.Domain → Bool ⊕ unifSpec.Domain
  | .inl input => .inl (target input)
  | .inr coin => .inr coin

omit [DecidableEq Digest] [SampleableType Digest] in
/-- Every miss is bounded by its source request; hits reuse the value and consume no digest draw. -/
theorem compiler_bound (target : Input → Bool) {X : Type} (client : OracleComp (Spec Input Digest) X)
    (budget : Nat × Nat)
    (bounded : client.IsQueryBound budget (fun q => enabled (drawClass target q))
      (fun q => debit (drawClass target q))) (cache : Cache Input Digest) :
    ((simulateQ (compiler target) client).run cache).IsQueryBound budget enabled debit := by
  induction client using OracleComp.inductionOn generalizing budget cache with
  | pure value => simpa only [simulateQ_pure, StateT.run_pure] using isQueryBound_pure (value, cache) budget enabled debit
  | query_bind q next ih =>
      rw [isQueryBound_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      cases q with
      | inl input =>
          simp only [compiler, StateT.run]
          cases hit : cache input with
          | none =>
              simp only [bind_assoc, pure_bind, isQueryBound_query_bind_iff]
              exact ⟨bounded.1, fun digest => ih digest _ (bounded.2 digest) _⟩
          | some digest =>
              simp only [pure_bind]
              apply draw_budget_mono _ (debit (.inl (target input)) budget) budget ?_
                (ih digest _ (bounded.2 digest) cache)
              cases target input <;> simp only [debit] <;> omega
      | inr coin =>
          simp only [compiler, StateT.run, bind_assoc, pure_bind, isQueryBound_query_bind_iff]
          exact ⟨True.intro, fun reply => ih reply _ (bounded.2 reply) cache⟩

/-- The actual instrumented lazy-oracle collision flag obeys the two-class bound. Source client class caps are transported by the checked compiler, rather than postulated for a reduction. -/
theorem collision_bound [Fintype Digest] [MeasurableSpace Digest] [DiscreteMeasurableSpace Digest]
    (target : Input → Bool) {X : Type} (client : OracleComp (Spec Input Digest) X)
    (targets ordinary : Nat)
    (bounded : client.IsQueryBound (targets, ordinary) (fun q => enabled (drawClass target q))
      (fun q => debit (drawClass target q))) :
    𝒟[(fun result : X × (Cache Input Digest × History Digest) => result.2.2.bad) <$>
      (simulateQ (instrumented target) client).run (∅, History.empty)] {true} ≤
      ((targets * (targets + ordinary) : Nat) : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [← program_compile, Functor.map_map]
  exact empty_bound ((simulateQ (compiler target) client).run ∅) targets ordinary
    (compiler_bound target client _ bounded ∅)

end BeaconcryptCore.Computational.PqxdhRecordFactsCollisionOracle

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollisionOracle.query_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollisionOracle.query_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollisionOracle.program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollisionOracle.program_project

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollisionOracle.query_compile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollisionOracle.query_compile

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollisionOracle.interpreter_compile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollisionOracle.interpreter_compile

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollisionOracle.program_compile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollisionOracle.program_compile

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollisionOracle.draw_budget_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollisionOracle.draw_budget_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollisionOracle.compiler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollisionOracle.compiler_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollisionOracle.collision_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollisionOracle.collision_bound


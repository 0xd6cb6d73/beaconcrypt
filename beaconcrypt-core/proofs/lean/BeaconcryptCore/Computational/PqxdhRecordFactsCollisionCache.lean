-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsCollisionOracle

/-! Cache collisions are witnessed by the actual chronological digest draw experiment. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsCollisionCache
open PqxdhRecordFactsCollision PqxdhRecordFactsCollisionOracle
variable {Input Digest : Type} [DecidableEq Input] [DecidableEq Digest]

/-- The digest list for one query class, retaining repeated answers. -/
def pool (history : History Digest) (target : Bool) : List Digest :=
  if target then history.targets else history.ordinary

/-- Every cached answer was drawn in its declared class. -/
def Recorded (target : Input → Bool) (cache : Cache Input Digest) (history : History Digest) : Prop :=
  ∀ input digest, cache input = some digest → digest ∈ pool history (target input)

/-- An equality between distinct cached inputs involving a target has already set the collision flag. -/
def Separated (target : Input → Bool) (cache : Cache Input Digest) (history : History Digest) : Prop :=
  ∀ left right digest, left ≠ right → (target left = true ∨ target right = true) →
    cache left = some digest → cache right = some digest → history.bad = true

/-- Recording a new draw retains every old class-list member. -/
theorem pool_mono (history : History Digest) (kind queried : Bool) (fresh value : Digest)
    (member : value ∈ pool history queried) :
    value ∈ pool (history.insert kind fresh) queried := by
  cases kind <;> cases queried <;> simp_all [pool, History.insert]

/-- The collision flag is absorbing. -/
theorem bad_mono (history : History Digest) (kind : Bool) (value : Digest)
    (bad : history.bad = true) : (history.insert kind value).bad = true := by
  cases kind <;> simp [History.insert, bad]

/-- Cache insertion retains actual draw provenance for every input, including unrelated coordinates. -/
theorem recorded_insert (target : Input → Bool) (cache : Cache Input Digest) (history : History Digest)
    (recorded : Recorded target cache history) (input : Input) (value : Digest) :
    Recorded target (cache.cacheQuery input value) (history.insert (target input) value) := by
  intro queried digest present
  by_cases same : queried = input
  · subst queried
    rw [QueryCache.cacheQuery_self] at present
    cases present
    cases target input <;> simp [pool, History.insert]
  · rw [QueryCache.cacheQuery_of_ne cache value same] at present
    exact pool_mono history (target input) (target queried) value digest (recorded queried digest present)

/-- A new value equal to an earlier value sets the flag when at least one belongs to the target class. -/
theorem hit_bad (history : History Digest) (kind other : Bool) (value : Digest)
    (targeted : kind = true ∨ other = true) (member : value ∈ pool history other) :
    (history.insert kind value).bad = true := by
  cases kind <;> cases other <;> simp_all [pool, History.insert, List.mem_append]

/-- Every equality at distinct cache inputs involving a target is tracked by the same actual flag after insertion. -/
theorem separated_insert (target : Input → Bool) (cache : Cache Input Digest) (history : History Digest)
    (recorded : Recorded target cache history) (separated : Separated target cache history)
    (input : Input) (value : Digest) :
    Separated target (cache.cacheQuery input value) (history.insert (target input) value) := by
  intro left right digest different targeted atLeft atRight
  by_cases leftNew : left = input
  · subst left
    rw [QueryCache.cacheQuery_self] at atLeft
    cases atLeft
    rw [QueryCache.cacheQuery_of_ne cache value (Ne.symm different)] at atRight
    exact hit_bad history (target input) (target right) value targeted (recorded right value atRight)
  · rw [QueryCache.cacheQuery_of_ne cache value leftNew] at atLeft
    by_cases rightNew : right = input
    · subst right
      rw [QueryCache.cacheQuery_self] at atRight
      cases atRight
      exact hit_bad history (target input) (target left) value targeted.symm (recorded left value atLeft)
    · rw [QueryCache.cacheQuery_of_ne cache value rightNew] at atRight
      exact bad_mono history (target input) value (separated left right digest different targeted atLeft atRight)

/-- The invariant records both draw provenance and the exact direction of event containment. -/
def Good (target : Input → Bool) (state : Cache Input Digest × History Digest) : Prop :=
  Recorded target state.1 state.2 ∧ Separated target state.1 state.2

omit [DecidableEq Input] [DecidableEq Digest] in
/-- The actual empty cache and draw ledger satisfy the invariant. -/
theorem initial_good (target : Input → Bool) : Good (Digest := Digest) target (∅, History.empty) := by
  constructor
  · intro input digest present
    simp at present
  · intro left right digest different targeted present
    simp at present

/-- Every supported query result preserves cache provenance and collision containment. -/
theorem query_good [SampleableType Digest] (target : Input → Bool) (q : (Spec Input Digest).Domain)
    (state : Cache Input Digest × History Digest) (good : Good target state)
    (result : (Spec Input Digest).Range q × (Cache Input Digest × History Digest))
    (reached : result ∈ support ((instrumented target q).run state)) : Good target result.2 := by
  cases q with
  | inl input =>
      simp only [instrumented, StateT.run] at reached
      cases hit : state.1 input with
      | none =>
          simp only [hit, bind_pure_comp, support_map] at reached
          obtain ⟨digest, drawn, rfl⟩ := reached
          exact ⟨recorded_insert target state.1 state.2 good.1 input digest,
            separated_insert target state.1 state.2 good.1 good.2 input digest⟩
      | some digest =>
          simp only [hit, support_pure, Set.mem_singleton_iff] at reached
          exact reached ▸ good
  | inr coin =>
      simp only [instrumented, StateT.run, support_map] at reached
      obtain ⟨reply, drawn, rfl⟩ := reached
      exact good

/-- The invariant holds through every adaptive client and every supported complete result. -/
theorem program_good [SampleableType Digest] (target : Input → Bool) {X : Type}
    (client : OracleComp (Spec Input Digest) X) (state : Cache Input Digest × History Digest)
    (good : Good target state) (result : X × (Cache Input Digest × History Digest))
    (reached : result ∈ support ((simulateQ (instrumented target) client).run state)) :
    Good target result.2 :=
  PqxdhRecordLiftFlat.support_keep_oracle (instrumented target) (Good target)
    (fun q before valid after supported => query_good target q before valid after supported)
    client state good result reached

/-- A concrete cache collision between distinct queried inputs, involving at least one target input. -/
def Collision (target : Input → Bool) (cache : Cache Input Digest) : Prop :=
  ∃ left right digest, left ≠ right ∧ (target left = true ∨ target right = true) ∧
    cache left = some digest ∧ cache right = some digest

/-- On the actual initialized run, a concrete cache collision implies the chronological draw flag. -/
theorem collision_detected [SampleableType Digest] (target : Input → Bool) {X : Type}
    (client : OracleComp (Spec Input Digest) X) (result : X × (Cache Input Digest × History Digest))
    (reached : result ∈ support ((simulateQ (instrumented target) client).run (∅, History.empty)))
    (collision : Collision target result.2.1) : result.2.2.bad = true := by
  obtain ⟨left, right, digest, different, targeted, atLeft, atRight⟩ := collision
  exact (program_good target client _ (initial_good target) result reached).2
    left right digest different targeted atLeft atRight

/-- Distinct-input cache collisions in the original lazy-oracle experiment obey the explicit source request caps. -/
theorem cache_collision_bound [SampleableType Digest] [Fintype Digest]
    [MeasurableSpace Digest] [DiscreteMeasurableSpace Digest]
    (target : Input → Bool) {X : Type} (client : OracleComp (Spec Input Digest) X)
    (targets ordinary : Nat)
    (bounded : client.IsQueryBound (targets, ordinary) (fun q => enabled (drawClass target q))
      (fun q => debit (drawClass target q))) :
    𝒟[(fun result : X × Cache Input Digest => @decide (Collision target result.2) (Classical.propDecidable _)) <$>
      (simulateQ plain client).run ∅] {true} ≤
      ((targets * (targets + ordinary) : Nat) : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ := by
  have projected := program_project target client ((∅, History.empty) : Cache Input Digest × History Digest)
  classical
  refine le_trans ?_ (collision_bound target client targets ordinary bounded)
  rw [← projected]
  simp only [Functor.map_map]
  simp only [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map]
  apply probEvent_mono
  intro result reached collision
  exact collision_detected target client result reached (of_decide_eq_true collision)

/-- The actual 512-bit commitment digest gives the stated denominator, for the original memoizing oracle rather than independent samples substituted at cache hits. -/
theorem ctx_cache_collision_bound (target : Input → Bool) {X : Type}
    (client : OracleComp (Spec Input CtxRomAuth.CtxDigest) X) (targets ordinary : Nat)
    (bounded : client.IsQueryBound (targets, ordinary) (fun q => enabled (drawClass target q))
      (fun q => debit (drawClass target q))) :
    𝒟[(fun result : X × Cache Input CtxRomAuth.CtxDigest =>
      @decide (Collision target result.2) (Classical.propDecidable _)) <$>
      (simulateQ plain client).run ∅] {true} ≤
      ((targets * (targets + ordinary) : Nat) : ENNReal) / (2 : ENNReal)^512 := by
  let _ : MeasurableSpace CtxRomAuth.CtxDigest := ⊤
  let _ : DiscreteMeasurableSpace CtxRomAuth.CtxDigest := ⟨fun _ => by simp⟩
  simpa only [CtxRomAuth.ctxDigest_card, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv] using
    cache_collision_bound target client targets ordinary bounded

end BeaconcryptCore.Computational.PqxdhRecordFactsCollisionCache

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollisionCache.pool_mono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollisionCache.pool_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollisionCache.bad_mono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollisionCache.bad_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollisionCache.recorded_insert' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollisionCache.recorded_insert

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollisionCache.hit_bad' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollisionCache.hit_bad

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollisionCache.separated_insert' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollisionCache.separated_insert

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollisionCache.initial_good' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollisionCache.initial_good

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollisionCache.query_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollisionCache.query_good

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollisionCache.program_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollisionCache.program_good

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollisionCache.collision_detected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollisionCache.collision_detected

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollisionCache.cache_collision_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollisionCache.cache_collision_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsCollisionCache.ctx_cache_collision_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsCollisionCache.ctx_cache_collision_bound


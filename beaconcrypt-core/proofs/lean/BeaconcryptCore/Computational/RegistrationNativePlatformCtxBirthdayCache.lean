-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayDraw
import BeaconcryptCore.Computational.PqxdhRecordFactsCollisionCache
/-! Tight collision accounting for the complete memoizing hash oracle, retaining an arbitrary known warm singleton. All hash inputs belong to the target class; interleaved client coins remain unchanged. The resource premise counts the actual future hash requests syntactically. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 400000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCache
open PqxdhRecordFactsCollision (History enabled debit)
open PqxdhRecordFactsCollisionOracle (Spec Cache plain instrumented compiler drawClass)
open PqxdhRecordFactsCollisionCache (Good Collision)
variable {Input Digest A : Type} [DecidableEq Input] [DecidableEq Digest]

/-- Count hash requests before cache lookup; arbitrary ordinary coins have zero hash cost. -/
def IsHash : Input ⊕ unifSpec.Domain → Prop
  | .inl _ => True
  | .inr _ => False
instance : DecidablePred (IsHash (Input := Input)) := fun query => by
  cases query <;> dsimp [IsHash] <;> infer_instance

omit [DecidableEq Input] [DecidableEq Digest] in
/-- A source hash cap gives a target-only draw budget without counting the interleaved coins. -/
theorem request_budget (client : OracleComp (Spec Input Digest) A) (future : Nat)
    (bounded : client.IsQueryBoundP IsHash future) :
    client.IsQueryBound (future, 0) (fun query => enabled (drawClass (fun _ => true) query))
      (fun query => debit (drawClass (fun _ => true) query)) := by
  induction client using OracleComp.inductionOn generalizing future with
  | pure value => trivial
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    rw [isQueryBound_query_bind_iff]
    cases query with
    | inl input =>
      constructor
      · simpa only [IsHash, not_true_eq_false, false_or, enabled, drawClass] using bounded.1
      · intro digest
        exact ih digest (future - 1) (bounded.2 digest)
    | inr coin =>
      constructor
      · trivial
      · intro reply
        exact ih reply future (bounded.2 reply)

omit [DecidableEq Digest] in
/-- A known singleton cache records its exact earlier value without requiring that value to be fresh or hidden. -/
theorem singleton_good (input : Input) (digest : Digest) :
    Good (fun _ => true) (((∅ : Cache Input Digest).cacheQuery input digest), ⟨[digest], [], false⟩) := by
  constructor
  · intro queried value present
    by_cases same : queried = input
    · subst queried
      rw [QueryCache.cacheQuery_self] at present
      cases present
      simp [PqxdhRecordFactsCollisionCache.pool]
    · rw [QueryCache.cacheQuery_of_ne _ _ same] at present
      simp at present
  · intro left right value different _targeted atLeft atRight
    have leftSame : left = input := by
      by_contra distinct
      rw [QueryCache.cacheQuery_of_ne _ _ distinct] at atLeft
      simp at atLeft
    have rightSame : right = input := by
      by_contra distinct
      rw [QueryCache.cacheQuery_of_ne _ _ distinct] at atRight
      simp at atRight
    exact False.elim (different (leftSame.trans rightSame.symm))

/-- The warm start contains the actual empty cache or exactly one retained input/value pair. -/
def Warm (cache : Cache Input Digest) : Prop :=
  cache = ∅ ∨ ∃ input digest, cache = (∅ : Cache Input Digest).cacheQuery input digest

variable [SampleableType Digest] [Fintype Digest] [MeasurableSpace Digest] [DiscreteMeasurableSpace Digest]

/-- Every actual cache miss uses the same tight draw experiment, including a clean reached history. -/
theorem instrumented_bound (client : OracleComp (Spec Input Digest) A) (future : Nat)
    (bounded : client.IsQueryBoundP IsHash future) (cache : Cache Input Digest)
    (history : History Digest) (clean : history.bad = false) :
    𝒟[(fun result : A × (Cache Input Digest × History Digest) => result.2.2.bad) <$>
      (simulateQ (instrumented (fun _ => true)) client).run (cache, history)] {true} ≤
      (RegistrationNativePlatformCtxBirthdayDraw.potential future (history.targets.length + history.ordinary.length) : ENNReal) *
        (Fintype.card Digest : ENNReal)⁻¹ := by
  rw [← PqxdhRecordFactsCollisionOracle.program_compile, Functor.map_map]
  exact RegistrationNativePlatformCtxBirthdayDraw.run_bound
    ((simulateQ (compiler (fun _ => true)) client).run cache) future
    (PqxdhRecordFactsCollisionOracle.compiler_bound _ client _ (request_budget client future bounded) cache) history clean

/-- Structural cache provenance transfers distinct-input collisions to the chronological flag, preserving complete replies and cache. -/
theorem collision_bound (client : OracleComp (Spec Input Digest) A) (future : Nat)
    (bounded : client.IsQueryBoundP IsHash future) (cache : Cache Input Digest)
    (history : History Digest) (good : Good (fun _ => true) (cache, history)) (clean : history.bad = false) :
    𝒟[(fun result : A × Cache Input Digest => @decide (Collision (fun _ => true) result.2) (Classical.propDecidable _)) <$>
      (simulateQ plain client).run cache] {true} ≤
      (RegistrationNativePlatformCtxBirthdayDraw.potential future (history.targets.length + history.ordinary.length) : ENNReal) *
        (Fintype.card Digest : ENNReal)⁻¹ := by
  have projected := PqxdhRecordFactsCollisionOracle.program_project (fun _ => true) client (cache, history)
  classical
  refine le_trans ?_ (instrumented_bound client future bounded cache history clean)
  rw [← projected]
  simp only [Functor.map_map]
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map]
  apply prEvent_mono_of_support
  intro result reached collision
  obtain ⟨left, right, digest, different, targeted, atLeft, atRight⟩ := of_decide_eq_true collision
  exact (PqxdhRecordFactsCollisionCache.program_good (fun _ => true) client (cache, history) good result reached).2
    left right digest different targeted atLeft atRight

/-- Any clean structurally recorded warm cache with at most one earlier digest has the exact one-prior birthday cap. -/
theorem warm_history_bound (client : OracleComp (Spec Input Digest) A) (future : Nat)
    (bounded : client.IsQueryBoundP IsHash future) (cache : Cache Input Digest)
    (history : History Digest) (good : Good (fun _ => true) (cache, history))
    (clean : history.bad = false) (prior : history.targets.length + history.ordinary.length ≤ 1) :
    𝒟[(fun result : A × Cache Input Digest => @decide (Collision (fun _ => true) result.2) (Classical.propDecidable _)) <$>
      (simulateQ plain client).run cache] {true} ≤
      ((future + 1).choose 2 : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ := by
  refine (collision_bound client future bounded cache history good clean).trans ?_
  apply mul_le_mul (Nat.cast_le.mpr ?_) le_rfl (by positivity) (by positivity)
  have monotone := Nat.add_le_add_right (Nat.mul_le_mul_left future prior) (future.choose 2)
  have tight : RegistrationNativePlatformCtxBirthdayDraw.potential future 1 = (future + 1).choose 2 := by
    simp only [RegistrationNativePlatformCtxBirthdayDraw.potential, Nat.mul_one, Nat.choose_succ_succ, Nat.choose_one_right]
  exact monotone.trans tight.le

/-- The unmodified lazy oracle starts empty and pays each pair among future misses only once. -/
theorem empty_bound (client : OracleComp (Spec Input Digest) A) (future : Nat)
    (bounded : client.IsQueryBoundP IsHash future) :
    𝒟[(fun result : A × Cache Input Digest => @decide (Collision (fun _ => true) result.2) (Classical.propDecidable _)) <$>
      (simulateQ plain client).run ∅] {true} ≤
      (future.choose 2 : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ := by
  simpa only [RegistrationNativePlatformCtxBirthdayDraw.potential, History.empty, List.length_nil,
    Nat.add_zero, Nat.mul_zero, Nat.zero_add] using
    collision_bound client future bounded ∅ History.empty (PqxdhRecordFactsCollisionCache.initial_good _) rfl

/-- A singleton is retained at its original input and exact known value throughout the same adaptive cache execution. -/
theorem singleton_bound (client : OracleComp (Spec Input Digest) A) (future : Nat)
    (bounded : client.IsQueryBoundP IsHash future) (input : Input) (digest : Digest) :
    𝒟[(fun result : A × Cache Input Digest => @decide (Collision (fun _ => true) result.2) (Classical.propDecidable _)) <$>
      (simulateQ plain client).run ((∅ : Cache Input Digest).cacheQuery input digest)] {true} ≤
      ((future + 1).choose 2 : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ :=
  warm_history_bound client future bounded _ ⟨[digest], [], false⟩ (singleton_good input digest) rfl (by simp)

/-- Empty and singleton warm starts share the same uniform bound, with no premise on the client's eventual success or earlier digest's distribution. -/
theorem warm_bound (client : OracleComp (Spec Input Digest) A) (future : Nat)
    (bounded : client.IsQueryBoundP IsHash future) (cache : Cache Input Digest) (warm : Warm cache) :
    𝒟[(fun result : A × Cache Input Digest => @decide (Collision (fun _ => true) result.2) (Classical.propDecidable _)) <$>
      (simulateQ plain client).run cache] {true} ≤
      ((future + 1).choose 2 : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹ := by
  rcases warm with empty | ⟨input, digest, rfl⟩
  · subst cache
    exact warm_history_bound client future bounded ∅ History.empty
      (PqxdhRecordFactsCollisionCache.initial_good _) rfl (by simp [History.empty])
  · exact singleton_bound client future bounded input digest

omit [DecidableEq Digest] [SampleableType Digest] [Fintype Digest] [MeasurableSpace Digest] [DiscreteMeasurableSpace Digest] in
/-- Exact 512-bit denominator for the actual warm memoizing CTX oracle, under the future source hash cap. -/
theorem ctx_warm_bound (client : OracleComp (Spec Input CtxRomAuth.CtxDigest) A) (future : Nat)
    (bounded : client.IsQueryBoundP IsHash future) (cache : Cache Input CtxRomAuth.CtxDigest) (warm : Warm cache) :
    𝒟[(fun result : A × Cache Input CtxRomAuth.CtxDigest =>
      @decide (Collision (fun _ => true) result.2) (Classical.propDecidable _)) <$>
      (simulateQ plain client).run cache] {true} ≤
      ((future + 1).choose 2 : ENNReal) / (2 : ENNReal)^512 := by
  let _ : MeasurableSpace CtxRomAuth.CtxDigest := ⊤
  let _ : DiscreteMeasurableSpace CtxRomAuth.CtxDigest := ⟨fun _ => by simp⟩
  simpa only [CtxRomAuth.ctxDigest_card, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv] using
    warm_bound client future bounded cache warm

end BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCache

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCache.request_budget' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCache.request_budget

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCache.singleton_good' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCache.singleton_good

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCache.instrumented_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCache.instrumented_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCache.collision_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCache.collision_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCache.warm_history_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCache.warm_history_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCache.empty_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCache.empty_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCache.singleton_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCache.singleton_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCache.warm_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCache.warm_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCache.ctx_warm_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayCache.ctx_warm_bound

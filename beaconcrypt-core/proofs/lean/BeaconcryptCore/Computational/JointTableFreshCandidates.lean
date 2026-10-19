import BeaconcryptCore.Computational.JointEagerTable

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.JointTableFreshCandidates

open JointEagerTable
variable {D R : Type} [DecidableEq D] [Finite D] [Finite R] [Nonempty R]
  [SampleableType R] [SampleableType (D → R)] [MeasurableSpace R]
  [DiscreteMeasurableSpace R]

/-- Any fixed coordinate of the independent completed tail is uniform. -/
theorem uniform_coordinate (point : D) :
    𝒟[(fun table : D → R => table point) <$> ($ᵗ (D → R))] = 𝒟[$ᵗ R] := by
  have law := evalDist_uniformSample_bind_update_map (R := R)
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample
    point (fun table => table point)
  simp only [Function.update_self, bind_pure_comp] at law
  rw [← law]
  trans 𝒟[($ᵗ R) >>= fun value => pure value]
  · apply evalDist_bind_congr
    intro value
    rw [OracleComp.evalDist_map_const, evalDist_pure]
  · rw [bind_pure]

/-- A candidate wins only at a final cache miss; each such fixed guess costs at most one uniform range value. Cached coordinates make this event false. -/
theorem fixed_fresh_guess_bound (cache : (D →ₒ R).QueryCache) (point : D) (guess : R) :
    Pr[ (fun table : D → R => cache point = none ∧ tableExtending cache table point = guess)
      | $ᵗ (D → R)] ≤ (Nat.card R : ℝ≥0∞)⁻¹ := by
  classical
  let := Fintype.ofFinite R
  by_cases fresh : cache point = none
  · have coordinate : Pr[(fun table : D → R => table point = guess) | $ᵗ (D → R)] =
        (Nat.card R : ℝ≥0∞)⁻¹ := by
      rw [← probOutput_map]
      rw [← evalDist_apply_singleton, uniform_coordinate, evalDist_apply_singleton,
        probOutput_uniformSample, Nat.card_eq_fintype_card]
    simpa only [tableExtending, fresh, Option.getD_none, true_and] using coordinate.le
  · simp [fresh]

/-- Absence is part of the winning event itself; an omitted candidate never wins. -/
def FreshHit (cache : (D →ₒ R).QueryCache) (table : D → R) : Option (D × R) → Prop
  | none => False
  | some (point, guess) => cache point = none ∧ table point = guess

/-- Optional candidates cover malformed and ineligible raw slots without dropping their accounting positions. -/
theorem optional_fresh_guess_bound (cache : (D →ₒ R).QueryCache) (candidate : Option (D × R)) :
    Pr[(fun tail : D → R => FreshHit cache (tableExtending cache tail) candidate) | $ᵗ (D → R)] ≤
      (Nat.card R : ℝ≥0∞)⁻¹ := by
  cases candidate with
  | none => simp [FreshHit]
  | some pair => exact fixed_fresh_guess_bound cache pair.1 pair.2

/-- The union bound counts every candidate slot, with no distinct-address or distinct-guess premise. -/
theorem fixed_vector_bound {bound : ℕ} (cache : (D →ₒ R).QueryCache)
    (candidates : List.Vector (Option (D × R)) bound) :
    Pr[(fun tail : D → R => ∃ index : Fin bound,
      FreshHit cache (tableExtending cache tail) (candidates.get index)) | $ᵗ (D → R)] ≤
      (bound : ℝ≥0∞) * (Nat.card R : ℝ≥0∞)⁻¹ := by
  classical
  calc
    _ ≤ ∑ index : Fin bound,
        Pr[(fun tail : D → R => FreshHit cache (tableExtending cache tail) (candidates.get index))
          | $ᵗ (D → R)] := by
      simpa using probEvent_exists_finset_le_sum (Finset.univ : Finset (Fin bound)) ($ᵗ (D → R))
        (fun index tail => FreshHit cache (tableExtending cache tail) (candidates.get index))
    _ ≤ ∑ _index : Fin bound, (Nat.card R : ℝ≥0∞)⁻¹ := by
      exact Finset.sum_le_sum fun index _ => optional_fresh_guess_bound cache (candidates.get index)
    _ = _ := by simp

/-- Retain the entire actual sampled result and final cache while independently completing only its missing table cells. -/
def completeResult {Result : Type} (draw : ProbComp (Result × (D →ₒ R).QueryCache)) :
    ProbComp ((D → R) × (Result × (D →ₒ R).QueryCache)) := do
  let result ← draw
  let tail ← $ᵗ (D → R)
  pure (tableExtending result.2 tail, result)

/-- Candidate selection may depend on the complete sampled result and final cache. Conditioned on those values, each absent-cell guess uses only the independent completion tail. -/
theorem completed_result_vector_bound {Result : Type} {bound : ℕ}
    (draw : ProbComp (Result × (D →ₒ R).QueryCache))
    (candidates : Result × (D →ₒ R).QueryCache → List.Vector (Option (D × R)) bound) :
    Pr[(fun terminal => ∃ index : Fin bound,
      FreshHit terminal.2.2 terminal.1 ((candidates terminal.2).get index)) | completeResult draw] ≤
      (bound : ℝ≥0∞) * (Nat.card R : ℝ≥0∞)⁻¹ := by
  unfold completeResult
  apply probEvent_bind_le_of_forall_le
  intro result _
  simpa only [bind_pure_comp, probEvent_map, Function.comp_def] using
    fixed_vector_bound result.2 (candidates result)

/-- The bound applies to an arbitrary adaptive mixed client, from any preexisting dictionary. Every explicit source coin remains part of its actual execution; malformed slots and repeated guesses remain in the fixed candidate vector. -/
theorem mixed_completed_vector_bound {Result : Type} {bound : ℕ}
    (client : OracleComp (MixedSpec D R) Result) (cache : (D →ₒ R).QueryCache)
    (candidates : Result × (D →ₒ R).QueryCache → List.Vector (Option (D × R)) bound) :
    Pr[(fun terminal => ∃ index : Fin bound,
      FreshHit terminal.2.2 terminal.1 ((candidates terminal.2).get index)) |
      completeResult ((simulateQ mixedLazyImpl client).run cache)] ≤
      (bound : ℝ≥0∞) / Nat.card R := by
  simpa only [div_eq_mul_inv] using
    completed_result_vector_bound ((simulateQ mixedLazyImpl client).run cache) candidates

end BeaconcryptCore.Computational.JointTableFreshCandidates

/--
info: 'BeaconcryptCore.Computational.JointTableFreshCandidates.uniform_coordinate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.JointTableFreshCandidates.uniform_coordinate

/--
info: 'BeaconcryptCore.Computational.JointTableFreshCandidates.fixed_fresh_guess_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.JointTableFreshCandidates.fixed_fresh_guess_bound

/--
info: 'BeaconcryptCore.Computational.JointTableFreshCandidates.fixed_vector_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.JointTableFreshCandidates.fixed_vector_bound

/--
info: 'BeaconcryptCore.Computational.JointTableFreshCandidates.completed_result_vector_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.JointTableFreshCandidates.completed_result_vector_bound

/--
info: 'BeaconcryptCore.Computational.JointTableFreshCandidates.mixed_completed_vector_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.JointTableFreshCandidates.mixed_completed_vector_bound

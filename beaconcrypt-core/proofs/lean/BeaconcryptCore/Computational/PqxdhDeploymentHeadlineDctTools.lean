-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHiddenLayout
import BeaconcryptCore.Computational.PqxdhFullSecretInputKdf
import VCVio.EvalDist.Expectation

/-!
# Generic tools of CE-12 D-ct (closing `ctGapTerm`)

Information-theoretic counting tools for the two statistical terms of `ctgap_world`: the averaged union bound of a lazily sampled table against one uniform hidden key, and the birthday bound of a lazily sampled digest cache. Nothing here is a cryptographic assumption; every statement is about uniform sampling, VCVio's lazy random oracle and expected values.

- Budgeted supermartingale. `expected_run_bounded`: if a potential indexed by a remaining budget does not increase in expectation at a free query and spends at most one unit at a costly one, then over a whole simulation whose costly queries are bounded by `b` (`IsQueryBoundP`) the expected final potential at budget 0 is at most the initial potential at budget `b`. The case without costly queries is P2b's `PqxdhDeploymentHeadlineCtGhost.expected_run_le`.
- Table against a hidden key. For a fixed function `Φ` from table values to keys, `mass Φ k` is the chance that `Φ` of a fresh uniform table value is `k`, `hits Φ T k` the number of entries of the table `T` whose value maps to `k`, and `size T` the number of entries. At the draw of a uniform key the expected hits are `size T / |W|` (`hits_draw`), and the expected mass of a uniform key is at most `1/|W|` whatever `Φ` is (`average_mass`): this is the averaging over the uniform marginal of the hidden key, with no property of `Φ` and no independence of the key from anything else. One read of the lazy random oracle adds at most `mass Φ k` to the hits (`ro_hits`) and at most one entry (`ro_size`).
- Birthday step. One read of the lazy random oracle on a digest cache creates a collision between two distinct inputs (`CollIn`) with chance at most `size C / |V|` (`ro_coll`), and `birthday_step` is the arithmetic identity of the counted birthday potential.
- `chance_le_expected` bounds the probability of a Boolean event by the expected value of any potential that is at least one on the event over the support.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools
open OracleComp.EvalDist (expectedValue)

/-! ### A budgeted supermartingale over a whole simulation -/

section Budget
variable {ι' : Type} {spec : OracleSpec ι'} {σ α : Type}

/-- A potential indexed by a remaining budget of costly queries: a costly query may spend one unit, a free one none. Then the expected final potential at budget 0 is at most the initial potential at the budget of the program. -/
theorem expected_run_bounded (impl : QueryImpl spec (StateT σ ProbComp)) (costly : ι' → Prop)
    [DecidablePred costly] (potential : ℕ → σ → ℝ≥0∞)
    (mono : ∀ b state, potential b state ≤ potential (b + 1) state)
    (paid : ∀ query state b, costly query →
      expectedValue ((impl query).run state) (fun result => potential b result.2) ≤ potential (b + 1) state)
    (free : ∀ query state b, ¬ costly query →
      expectedValue ((impl query).run state) (fun result => potential b result.2) ≤ potential b state)
    (work : OracleComp spec α) (b : ℕ) (bounded : work.IsQueryBoundP costly b) (state : σ) :
    expectedValue ((simulateQ impl work).run state) (fun result => potential 0 result.2) ≤ potential b state := by
  induction work using OracleComp.inductionOn generalizing state b with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, OracleComp.EvalDist.expectedValue_pure]
      clear bounded
      induction b with
      | zero => exact le_rfl
      | succ n ih => exact ih.trans (mono n state)
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      rw [simulateQ_query_bind, StateT.run_bind, OracleComp.EvalDist.expectedValue_bind]
      by_cases hq : costly query
      · obtain ⟨pos, rest⟩ := bounded
        have positive : 0 < b := pos.resolve_left (not_not.mpr hq)
        obtain ⟨n, rfl⟩ : ∃ n, b = n + 1 := ⟨b - 1, by omega⟩
        refine le_trans (OracleComp.EvalDist.expectedValue_mono ((impl query).run state) ?_) (paid query state n hq)
        intro result
        have bound := rest result.1
        simp only [hq, ite_true, Nat.add_sub_cancel] at bound
        exact ih result.1 n bound result.2
      · refine le_trans (OracleComp.EvalDist.expectedValue_mono ((impl query).run state) ?_) (free query state b hq)
        intro result
        have bound := bounded.2 result.1
        simp only [hq, ite_false] at bound
        exact ih result.1 b bound result.2

/-- The probability of a Boolean event is at most the expected value of any potential that is at least one on the event over the support. -/
theorem chance_le_expected (run : ProbComp α) (event : α → Bool) (potential : α → ℝ≥0∞)
    (above : ∀ a ∈ support run, event a = true → 1 ≤ potential a) :
    𝒟[event <$> run] {true} ≤ expectedValue run potential := by
  classical
  rw [← prEvent_eq_evalDist_singleton _ true, prEvent_map,
    ← VCVioLegacy.probEvent_eq_prEvent run (fun a => event a = true),
    ← OracleComp.EvalDist.expectedValue_ite_one]
  refine OracleComp.EvalDist.expectedValue_mono_of_support fun a supported => ?_
  by_cases holds : event a = true
  · simp only [holds, ↓reduceIte]
    exact above a supported holds
  · simp only [holds]
    exact zero_le

end Budget

/-! ### Averaging over the uniform hidden key -/

section Average
variable {V W : Type}

/-- `mass Φ k`: the chance that `Φ` of a fresh uniform table value is `k`. -/
noncomputable def mass [SampleableType V] [DecidableEq W] (Φ : V → W) (k : W) : ℝ≥0∞ :=
  expectedValue ($ᵗ V : ProbComp V) fun v => if Φ v = k then 1 else 0

/-- Exactly one key is `Φ v`. -/
theorem tsum_indicator [DecidableEq W] (Φ : V → W) (v : V) : ∑' k : W, (if Φ v = k then (1 : ℝ≥0∞) else 0) = 1 := by
  have flip : (fun k : W => if Φ v = k then (1 : ℝ≥0∞) else 0) = fun k => if k = Φ v then 1 else 0 :=
    funext fun k => by by_cases same : k = Φ v <;> simp [same, eq_comm]
  rw [flip, tsum_ite_eq]

/-- The averaged per-entry bound: whatever `Φ` is, the expected mass of a uniform key is at most `1/|W|`. -/
theorem average_mass [SampleableType V] [SampleableType W] [Fintype W] [DecidableEq W] (Φ : V → W) :
    expectedValue ($ᵗ W : ProbComp W) (mass Φ) ≤ (Fintype.card W : ℝ≥0∞)⁻¹ := by
  rw [OracleComp.EvalDist.expectedValue_def]
  simp only [VCVioLegacy.probOutput_eq_prEvent, SampleableType.prEvent_uniformSample_eq_singleton]
  rw [ENNReal.tsum_mul_left]
  calc (Fintype.card W : ℝ≥0∞)⁻¹ * ∑' k, mass Φ k ≤ (Fintype.card W : ℝ≥0∞)⁻¹ * 1 := by
        gcongr
        simp only [mass, OracleComp.EvalDist.expectedValue_def]
        rw [ENNReal.tsum_comm]
        simp only [ENNReal.tsum_mul_left, tsum_indicator, mul_one]
        simpa only [VCVioLegacy.probOutput_eq_prEvent] using OracleComp.tsum_prEvent_le_one ($ᵗ V : ProbComp V)
    _ = _ := mul_one _

/-- The first component of a uniform pair is uniform. -/
theorem expected_fst {α β : Type} [SampleableType α] [SampleableType β] (g : α → ℝ≥0∞) :
    expectedValue ($ᵗ (α × β) : ProbComp (α × β)) (fun m => g m.1) = expectedValue ($ᵗ α : ProbComp α) g := by
  rw [← PqxdhFullSecretInputKdf.pairSample, OracleComp.EvalDist.expectedValue_bind]
  congr 1
  funext a
  rw [OracleComp.EvalDist.expectedValue_bind]
  simp only [OracleComp.EvalDist.expectedValue_pure]
  exact OracleComp.EvalDist.expectedValue_const (probFailure_uniformSample _) (g a)

end Average

/-! ### Hits of a lazily sampled table against a key -/

section Table
variable {D V W : Type}

/-- A lazily sampled table (a VCVio query cache of one oracle). -/
abbrev Cache (D V : Type) := (D →ₒ V).QueryCache

/-- The number of table entries whose value maps to `k`. -/
noncomputable def hits [DecidableEq W] (Φ : V → W) (T : Cache D V) (k : W) : ℝ≥0∞ :=
  ∑' u, (T u).elim 0 fun v => if Φ v = k then 1 else 0

/-- The number of table entries. -/
noncomputable def size (T : Cache D V) : ℝ≥0∞ := ∑' u, (T u).elim 0 fun _ => 1

/-- At the draw of a uniform key every existing entry is hit with chance `1/|W|`. -/
theorem hits_draw [SampleableType W] [Fintype W] [DecidableEq W] (Φ : V → W) (T : Cache D V) :
    expectedValue ($ᵗ W : ProbComp W) (hits Φ T) = size T * (Fintype.card W : ℝ≥0∞)⁻¹ := by
  rw [OracleComp.EvalDist.expectedValue_def]
  simp only [VCVioLegacy.probOutput_eq_prEvent, SampleableType.prEvent_uniformSample_eq_singleton]
  rw [ENNReal.tsum_mul_left, mul_comm]
  congr 1
  unfold hits size
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun u => ?_
  cases T u with
  | none => simp
  | some v => simp

/-- A miss adds one entry to the hits. -/
theorem hits_cacheQuery [DecidableEq D] [DecidableEq W] (Φ : V → W) (T : Cache D V) (u : D) (fresh : T u = none) (v : V) (k : W) :
    hits Φ (T.cacheQuery u v) k = hits Φ T k + if Φ v = k then 1 else 0 := by
  unfold hits
  rw [ENNReal.tsum_eq_add_tsum_ite u, ENNReal.tsum_eq_add_tsum_ite (f := fun u' => (T u').elim 0 _) u]
  simp only [QueryCache.cacheQuery_self, fresh, Option.elim]
  rw [zero_add, add_comm]
  congr 1
  refine tsum_congr fun u' => ?_
  by_cases same : u' = u
  · simp [same]
  · simp [same]

/-- At a miss, a fresh uniform value adds `mass Φ k` to the hits in expectation. -/
theorem hits_miss [DecidableEq D] [SampleableType V] [DecidableEq W] (Φ : V → W) (T : Cache D V) (u : D) (fresh : T u = none) (k : W) :
    expectedValue ($ᵗ V : ProbComp V) (fun v => hits Φ (T.cacheQuery u v) k) ≤ hits Φ T k + mass Φ k := by
  simp only [hits_cacheQuery Φ T u fresh]
  rw [OracleComp.EvalDist.expectedValue_add]
  exact add_le_add (OracleComp.EvalDist.expectedValue_le_of_le _ fun _ => le_rfl) le_rfl

/-- A miss adds one entry. -/
theorem size_cacheQuery [DecidableEq D] (T : Cache D V) (u : D) (fresh : T u = none) (v : V) :
    size (T.cacheQuery u v) = size T + 1 := by
  unfold size
  rw [ENNReal.tsum_eq_add_tsum_ite u, ENNReal.tsum_eq_add_tsum_ite (f := fun u' => (T u').elim 0 _) u]
  simp only [QueryCache.cacheQuery_self, fresh, Option.elim]
  rw [zero_add, add_comm]
  congr 1
  refine tsum_congr fun u' => ?_
  by_cases same : u' = u
  · simp [same]
  · simp [same]

/-- An entry whose value maps to `k` counts once. -/
theorem one_le_hits [DecidableEq W] (Φ : V → W) (T : Cache D V) (u : D) (v : V) (found : T u = some v) :
    1 ≤ hits Φ T (Φ v) := by
  unfold hits
  refine le_trans (le_of_eq ?_) (ENNReal.le_tsum u)
  simp [found]

/-- One read of VCVio's lazy random oracle adds at most `mass Φ k` to the hits in expectation, whatever the cache. -/
theorem ro_hits [DecidableEq D] [SampleableType V] [DecidableEq W] (Φ : V → W) (T : Cache D V) (u : D) (k : W) :
    expectedValue (((D →ₒ V).randomOracle u).run T) (fun result => hits Φ result.2 k) ≤ hits Φ T k + mass Φ k := by
  cases found : T u with
  | some v =>
      rw [QueryImpl.withCaching_run_some _ found, OracleComp.EvalDist.expectedValue_pure]
      exact le_self_add
  | none =>
      rw [QueryImpl.withCaching_run_none _ found, OracleComp.EvalDist.expectedValue_map]
      exact hits_miss Φ T u found k

/-- One read of the lazy random oracle adds at most one entry in expectation. -/
theorem ro_size [DecidableEq D] [SampleableType V] (T : Cache D V) (u : D) :
    expectedValue (((D →ₒ V).randomOracle u).run T) (fun result => size result.2) ≤ size T + 1 := by
  cases found : T u with
  | some v =>
      rw [QueryImpl.withCaching_run_some _ found, OracleComp.EvalDist.expectedValue_pure]
      exact le_self_add
  | none =>
      rw [QueryImpl.withCaching_run_none _ found, OracleComp.EvalDist.expectedValue_map]
      refine OracleComp.EvalDist.expectedValue_le_of_le _ fun v => le_of_eq ?_
      exact size_cacheQuery T u found v

end Table

/-! ### The birthday step of a lazily sampled digest cache -/

section Birthday
variable {D V : Type}

/-- Two distinct inputs of a cache with one value. -/
def CollIn (C : Cache D V) : Prop := ∃ y z d, y ≠ z ∧ C y = some d ∧ C z = some d

/-- Entries equal to a given digest. -/
noncomputable def equalTo [DecidableEq V] (C : Cache D V) (d : V) : ℝ≥0∞ := ∑' z, if C z = some d then 1 else 0

/-- A uniform digest equals each cached digest with chance `1/|V|`. -/
theorem equalTo_draw [SampleableType V] [Fintype V] [DecidableEq V] (C : Cache D V) :
    expectedValue ($ᵗ V : ProbComp V) (equalTo C) = size C * (Fintype.card V : ℝ≥0∞)⁻¹ := by
  rw [OracleComp.EvalDist.expectedValue_def]
  simp only [VCVioLegacy.probOutput_eq_prEvent, SampleableType.prEvent_uniformSample_eq_singleton]
  rw [ENNReal.tsum_mul_left, mul_comm]
  congr 1
  unfold equalTo size
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun z => ?_
  cases C z with
  | none => simp
  | some w =>
      have flip : (fun d : V => if some w = some d then (1 : ℝ≥0∞) else 0) = fun d => if d = w then 1 else 0 :=
        funext fun d => by
          by_cases same : d = w
          · simp [same]
          · simp [same, Ne.symm same]
      simp only [Option.elim]
      rw [flip, tsum_ite_eq]

/-- A cached digest counts once. -/
theorem one_le_equalTo [DecidableEq V] (C : Cache D V) (z : D) (d : V) (found : C z = some d) : 1 ≤ equalTo C d := by
  unfold equalTo
  refine le_trans (le_of_eq ?_) (ENNReal.le_tsum z)
  simp [found]

/-- A collision after a miss is an old collision or a hit of the new digest on an old one. -/
theorem collIn_cacheQuery [DecidableEq D] (C : Cache D V) (u : D) (fresh : C u = none) (v : V) (coll : CollIn (C.cacheQuery u v)) :
    CollIn C ∨ ∃ z, C z = some v := by
  obtain ⟨y, z, d, different, atY, atZ⟩ := coll
  by_cases yu : y = u
  · subst yu
    rw [QueryCache.cacheQuery_self] at atY
    cases atY
    rw [QueryCache.cacheQuery_of_ne C v (Ne.symm different)] at atZ
    exact Or.inr ⟨z, atZ⟩
  · rw [QueryCache.cacheQuery_of_ne C v yu] at atY
    by_cases zu : z = u
    · subst zu
      rw [QueryCache.cacheQuery_self] at atZ
      cases atZ
      exact Or.inr ⟨y, atY⟩
    · rw [QueryCache.cacheQuery_of_ne C v zu] at atZ
      exact Or.inl ⟨y, z, d, different, atY, atZ⟩

open Classical in
/-- One read of the lazy random oracle creates a collision with chance at most `size C / |V|`. -/
theorem ro_coll [DecidableEq D] [SampleableType V] [Fintype V] [DecidableEq V] (C : Cache D V) (u : D) :
    expectedValue (((D →ₒ V).randomOracle u).run C) (fun r => if CollIn r.2 then (1 : ℝ≥0∞) else 0) ≤
      (if CollIn C then 1 else 0) + size C * (Fintype.card V : ℝ≥0∞)⁻¹ := by
  cases found : C u with
  | some v =>
      rw [QueryImpl.withCaching_run_some _ found, OracleComp.EvalDist.expectedValue_pure]
      exact le_self_add
  | none =>
      rw [QueryImpl.withCaching_run_none _ found, OracleComp.EvalDist.expectedValue_map, ← equalTo_draw C,
        ← OracleComp.EvalDist.expectedValue_const (probFailure_uniformSample V) (if CollIn C then (1 : ℝ≥0∞) else 0),
        ← OracleComp.EvalDist.expectedValue_add]
      refine OracleComp.EvalDist.expectedValue_mono _ fun v => ?_
      by_cases coll : CollIn (C.cacheQuery u v)
      · simp only [coll, ↓reduceIte]
        rcases collIn_cacheQuery C u found v coll with old | ⟨z, atZ⟩
        · simp only [old, ↓reduceIte]
          exact le_self_add
        · exact le_add_left (one_le_equalTo C z v atZ)
      · simp only [coll, ↓reduceIte]
        exact zero_le

/-- The arithmetic of the counted birthday potential: one counted draw against `m` cached digests. -/
theorem birthday_step (b m : ℕ) : (b + 1) * m + (b + 1).choose 2 = b * (m + 1) + b.choose 2 + m := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right]
  ring

end Birthday

/-! ### Key and digest sizes -/

/-- A 32-byte key part has `2^256` values. -/
theorem keyPart_card : Fintype.card RawCtxKdfRequestTable.KeyPart = 2 ^ 256 := by
  rw [card_vector]
  have hbyte : Fintype.card UInt8 = 256 := by
    set_option maxRecDepth 100000 in
      rfl
  rw [hbyte]
  calc
    256 ^ 32 = (2 ^ 8) ^ 32 := by norm_num
    _ = 2 ^ (8 * 32) := by rw [pow_mul]
    _ = 2 ^ 256 := by norm_num

/-- The key part of a uniform material is uniform (the nonce draw is integrated out). -/
theorem material_marginal (g : RawCtxKdfRequestTable.KeyPart → ℝ≥0∞) :
    expectedValue ($ᵗ PqxdhDeploymentHiddenLayout.Material : ProbComp PqxdhDeploymentHiddenLayout.Material)
      (fun m => g m.1) = expectedValue ($ᵗ RawCtxKdfRequestTable.KeyPart : ProbComp RawCtxKdfRequestTable.KeyPart) g :=
  expected_fst g

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.expected_run_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.expected_run_bounded

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.chance_le_expected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.chance_le_expected

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.tsum_indicator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.tsum_indicator

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.average_mass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.average_mass

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.expected_fst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.expected_fst

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.hits_draw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.hits_draw

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.hits_cacheQuery' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.hits_cacheQuery

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.hits_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.hits_miss

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.size_cacheQuery' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.size_cacheQuery

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.one_le_hits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.one_le_hits

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.ro_hits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.ro_hits

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.ro_size' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.ro_size

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.equalTo_draw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.equalTo_draw

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.one_le_equalTo' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.one_le_equalTo

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.collIn_cacheQuery' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.collIn_cacheQuery

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.ro_coll' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.ro_coll

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.birthday_step' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.birthday_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.keyPart_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.keyPart_card

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.material_marginal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTools.material_marginal

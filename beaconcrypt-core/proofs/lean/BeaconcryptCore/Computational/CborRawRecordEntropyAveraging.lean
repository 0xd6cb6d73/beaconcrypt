-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftFresh

/-! Finite byte-shift averaging and the test-bit counting identity apply to arbitrary complete computations. Their hypotheses are syntactic couplings, discharged for the actual cursor-aware world by its concrete interpreter. They do not posit a source-game equivalence or any cryptographic independence assumption. -/
open OracleComp OracleSpec ENNReal CoreModels Aeneas MeasureTheory
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordEntropyAveraging
open PqxdhRecordLiftIdeal PqxdhRecordLiftSwap PqxdhRecordLiftFresh
open PqxdhRecordLiftLor (lorEligible_split evalDist_or)
open PqxdhDeploymentInterface (FreshBounds)
variable {n : Nat} {E X : Type}

theorem hitAt_bound (bounds : FreshBounds) (claim : X → Option (Nat × Pqxdh.Bytes))
    (index length : Nat) (work : ProbComp (Client n E X × CtxPrivate n))
    (shifts : ∀ offsets : Fin length → Fin 256, Swap (fun first second =>
      hitAt claim index length (ctxView first) = shiftedHit bounds claim index length offsets (ctxView second)) work work) :
    𝒟[(fun result => hitAt claim index length (ctxView result)) <$> work] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ *
        𝒟[(fun result => keyAt claim index length (ctxView result)) <$> work] {true} := by
  have same : ∀ offsets : Fin length → Fin 256,
      𝒟[(fun result => hitAt claim index length (ctxView result)) <$>
          work] {true} =
        𝒟[(fun result => shiftedHit bounds claim index length offsets (ctxView result)) <$>
          work] {true} := fun offsets => by
    rw [(shifts offsets).evalDist_map _ _ fun _ _ related => related]
  let _ : MeasurableSpace (Client n E X × CtxPrivate n) := ⊤
  have _ : DiscreteMeasurableSpace (Client n E X × CtxPrivate n) := ⟨fun _ => trivial⟩
  by_cases short : length < bounds.min
  · rw [same (fun _ => 0), evalDist_map_true]
    have empty : {result : Client n E X × CtxPrivate n |
        shiftedHit bounds claim index length (fun _ => 0) (ctxView result) = true} = ∅ := by
      ext result
      simp only [shiftedHit, decide_eq_true_eq, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h
      omega
    rw [empty, measure_empty]
    exact zero_le
  · have long : bounds.min ≤ length := Nat.le_of_not_lt short
    have sum : ∑ offsets : Fin length → Fin 256,
        𝒟[(fun result => shiftedHit bounds claim index length offsets (ctxView result)) <$> work] {true} ≤
          𝒟[(fun result => keyAt claim index length (ctxView result)) <$> work] {true} := by
      simp only [evalDist_map_true]
      rw [← measure_biUnion_finset]
      · apply measure_mono
        intro result hresult
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_univ, exists_true_left] at hresult ⊢
        obtain ⟨offsets, hit⟩ := hresult
        exact shiftedHit_key bounds claim index length offsets _ hit
      · intro first _ second _ distinct
        exact Set.disjoint_left.mpr fun result h₁ h₂ =>
          distinct (shiftedHit_disjoint bounds claim index length first second _ h₁ h₂)
      · intro _ _
        exact .of_discrete
    have card : ∑ _offsets : Fin length → Fin 256,
        𝒟[(fun result => hitAt claim index length (ctxView result)) <$> work] {true} =
          ((256 ^ length : ℕ) : ℝ≥0∞) * 𝒟[(fun result => hitAt claim index length (ctxView result)) <$> work] {true} := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
    have scaled : ((256 ^ bounds.min : ℕ) : ℝ≥0∞) *
        𝒟[(fun result => hitAt claim index length (ctxView result)) <$> work] {true} ≤
          𝒟[(fun result => keyAt claim index length (ctxView result)) <$> work] {true} :=
      calc _ ≤ ((256 ^ length : ℕ) : ℝ≥0∞) *
            𝒟[(fun result => hitAt claim index length (ctxView result)) <$> work] {true} := by
            gcongr
        _ = ∑ offsets : Fin length → Fin 256,
            𝒟[(fun result => shiftedHit bounds claim index length offsets (ctxView result)) <$> work] {true} := by
            rw [← card]
            exact Finset.sum_congr rfl fun offsets _ => same offsets
        _ ≤ _ := sum
    exact (ENNReal.mul_le_iff_le_inv (by simp) (ENNReal.natCast_ne_top _)).mp scaled


theorem fresh_bound (bounds : FreshBounds) (claim : X → Option (Nat × Pqxdh.Bytes))
    (work : ProbComp (Client n E X × CtxPrivate n))
    (shifts : ∀ index length (offsets : Fin length → Fin 256), Swap (fun first second =>
      hitAt claim index length (ctxView first) = shiftedHit bounds claim index length offsets (ctxView second)) work work) :
    𝒟[(fun result => freshEvent claim (ctxView result)) <$> work] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ := by
  have bound := fun key : ℕ × ℕ =>
    hitAt_bound bounds claim key.1 key.2 work (shifts key.1 key.2)
  let _ : MeasurableSpace (Client n E X × CtxPrivate n) := ⊤
  have _ : DiscreteMeasurableSpace (Client n E X × CtxPrivate n) := ⟨fun _ => trivial⟩
  simp only [evalDist_map_true] at bound ⊢
  calc 𝒟[work] {result | freshEvent claim (ctxView result) = true}
      ≤ 𝒟[work] (⋃ key : ℕ × ℕ, {result | hitAt claim key.1 key.2 (ctxView result) = true}) := by
        apply measure_mono
        intro result hresult
        simp only [Set.mem_ofPred_eq, Set.mem_iUnion] at hresult ⊢
        exact freshEvent_cover claim _ hresult
    _ ≤ ∑' key : ℕ × ℕ, 𝒟[work] {result | hitAt claim key.1 key.2 (ctxView result) = true} :=
        measure_iUnion_le _
    _ ≤ ∑' key : ℕ × ℕ, ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ *
          𝒟[work] {result | keyAt claim key.1 key.2 (ctxView result) = true} := ENNReal.tsum_le_tsum bound
    _ = ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ *
          𝒟[work] (⋃ key : ℕ × ℕ, {result | keyAt claim key.1 key.2 (ctxView result) = true}) := by
        rw [ENNReal.tsum_mul_left, ← measure_iUnion]
        · intro first second distinct
          exact Set.disjoint_left.mpr fun result h₁ h₂ => distinct (keyAt_unique claim first second _ h₁ h₂)
        · intro _
          exact .of_discrete
    _ ≤ ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ * 1 := by
        gcongr
        exact (measure_mono (Set.subset_univ _)).trans (evalDist_apply_univ_le_one work)
    _ = ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ := mul_one _


theorem lor_half {Reader Response : Type} (crypto : Pqxdh.Crypto)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : Std.U64)
    (decision eligible : PublicHiding n E X → Bool) (work : ProbComp (Client n E X × CtxPrivate n))
    (swapped : Swap (fun first second =>
      lorGuess crypto codec serverKid decision eligible (ctxView first) =
        lorGuess crypto codec serverKid (fun projection => !decision projection) eligible (ctxView second)) work work) :
    𝒟[(fun result => lorGuess crypto codec serverKid decision eligible (ctxView result)) <$> work] {true} =
      2⁻¹ * 𝒟[(fun result => lorEligible crypto codec serverKid eligible (ctxView result)) <$> work] {true} := by
  have same := swapped.evalDist_map
    (fun result => lorGuess crypto codec serverKid decision eligible (ctxView result))
    (fun result => lorGuess crypto codec serverKid (fun projection => !decision projection) eligible
      (ctxView result)) fun _ _ related => related
  have split : (fun result : Client n E X × CtxPrivate n =>
      lorEligible crypto codec serverKid eligible (ctxView result)) =
      fun result => lorGuess crypto codec serverKid decision eligible (ctxView result) ||
        lorGuess crypto codec serverKid (fun projection => !decision projection) eligible (ctxView result) :=
    funext fun result => (lorEligible_split crypto codec serverKid decision eligible (ctxView result)).1
  rw [split, evalDist_or _ _ _ fun result =>
    (lorEligible_split crypto codec serverKid decision eligible (ctxView result)).2, ← same, ← two_mul,
    ← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]



end BeaconcryptCore.Computational.CborRawRecordEntropyAveraging

/-- info: 'BeaconcryptCore.Computational.CborRawRecordEntropyAveraging.hitAt_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordEntropyAveraging.hitAt_bound

/-- info: 'BeaconcryptCore.Computational.CborRawRecordEntropyAveraging.fresh_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordEntropyAveraging.fresh_bound

/-- info: 'BeaconcryptCore.Computational.CborRawRecordEntropyAveraging.lor_half' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordEntropyAveraging.lor_half

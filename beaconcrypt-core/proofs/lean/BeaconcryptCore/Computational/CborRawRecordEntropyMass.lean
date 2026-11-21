-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordEntropyAveraging

/-! Byte-shift averaging retains the mass of successful execution instead of replacing it by one. This form supports public selector masks: aborting only the final observation on unselected runs preserves the protocol execution and yields the selector-weighted entropy bound. -/
open OracleComp OracleSpec ENNReal CoreModels Aeneas MeasureTheory
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.CborRawRecordEntropyMass
open PqxdhRecordLiftIdeal PqxdhRecordLiftSwap PqxdhRecordLiftFresh
open PqxdhDeploymentInterface (FreshBounds)
variable {n : Nat} {E X : Type}

theorem keyAt_present (claim : X → Option (Nat × Pqxdh.Bytes)) (index length : Nat)
    (view : View n E X) (selected : keyAt claim index length view = true) : view.result.isSome = true := by
  cases present : view.result <;> simp_all [keyAt, freshKey]

/-- The per-index disjoint byte shifts charge only the mass of a returned execution. -/
theorem fresh_bound (bounds : FreshBounds) (claim : X → Option (Nat × Pqxdh.Bytes))
    (work : ProbComp (Client n E X × CtxPrivate n))
    (shifts : ∀ index length (offsets : Fin length → Fin 256), Swap (fun first second =>
      hitAt claim index length (ctxView first) = shiftedHit bounds claim index length offsets (ctxView second)) work work) :
    𝒟[(fun result => freshEvent claim (ctxView result)) <$> work] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ *
        𝒟[(fun result => (ctxView result).result.isSome) <$> work] {true} := by
  have bound := fun key : ℕ × ℕ =>
    CborRawRecordEntropyAveraging.hitAt_bound bounds claim key.1 key.2 work (shifts key.1 key.2)
  let _ : MeasurableSpace (Client n E X × CtxPrivate n) := ⊤
  have _ : DiscreteMeasurableSpace (Client n E X × CtxPrivate n) := ⟨fun _ => trivial⟩
  simp only [evalDist_map_true] at bound ⊢
  calc 𝒟[work] {result | freshEvent claim (ctxView result) = true}
      ≤ 𝒟[work] (⋃ key : ℕ × ℕ, {result | hitAt claim key.1 key.2 (ctxView result) = true}) := by
        exact measure_mono fun result winning => Set.mem_iUnion.mpr (freshEvent_cover claim _ winning)
    _ ≤ ∑' key : ℕ × ℕ, 𝒟[work] {result | hitAt claim key.1 key.2 (ctxView result) = true} :=
        measure_iUnion_le _
    _ ≤ ∑' key : ℕ × ℕ, ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ *
          𝒟[work] {result | keyAt claim key.1 key.2 (ctxView result) = true} := ENNReal.tsum_le_tsum bound
    _ = ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ *
          𝒟[work] (⋃ key : ℕ × ℕ, {result | keyAt claim key.1 key.2 (ctxView result) = true}) := by
        rw [ENNReal.tsum_mul_left, ← measure_iUnion]
        · exact fun first second distinct => Set.disjoint_left.mpr fun result h₁ h₂ =>
            distinct (keyAt_unique claim first second _ h₁ h₂)
        · exact fun _ => .of_discrete
    _ ≤ ((256 ^ bounds.min : ℕ) : ℝ≥0∞)⁻¹ *
          𝒟[work] {result | (ctxView result).result.isSome = true} := by
        gcongr
        exact fun result chosen => Exists.elim (Set.mem_iUnion.mp chosen) fun key selected =>
          keyAt_present claim key.1 key.2 _ selected

end BeaconcryptCore.Computational.CborRawRecordEntropyMass

/-- info: 'BeaconcryptCore.Computational.CborRawRecordEntropyMass.keyAt_present' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordEntropyMass.keyAt_present
/-- info: 'BeaconcryptCore.Computational.CborRawRecordEntropyMass.fresh_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordEntropyMass.fresh_bound

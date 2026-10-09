-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsCollision

/-! Average bounds over the unchanged supported prefix distribution. -/
open OracleComp OracleSpec ENNReal MeasureTheory ProbabilityTheory
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginAverage

/-- A continuation bound is needed only at supported prefix states; the original prefix is neither fixed nor conditioned on a later event. -/
theorem bind_le {X Y : Type} [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    (work : ProbComp X) (next : X → ProbComp Y) (event : Set Y) (cap : ℝ≥0∞)
    (bounded : ∀ value ∈ support work, 𝒟[next value] event ≤ cap) :
    𝒟[work >>= next] event ≤ cap := by
  change 𝒟[work >>= next] {value | value ∈ event} ≤ cap
  simp only [evalDist_apply_setOf]
  apply probEvent_bind_le_of_forall_le
  intro value supported
  simpa only [evalDist_apply_setOf] using (show 𝒟[next value] {result | result ∈ event} ≤ cap from bounded value supported)

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginAverage

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginAverage.bind_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginAverage.bind_le

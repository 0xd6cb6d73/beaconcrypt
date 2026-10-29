-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordObservation

/-! The same word-guessing bound retains the actual full final byte-oracle cache. A final observer may inspect the candidate, complete returned client state and that cache; only the executing oracle client must be candidate-free. The symbolic cache is evaluated by the explicit source lens, so no arbitrary table coordinate is silently discarded. -/
open OracleComp OracleSpec CoreModels ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordCachedObservation
open RegistrationNativeSecretWord (Spec Cache IsKey symbolic actual literals)
open RegistrationNativeSecretWordTrace (run guess_bound)
open RegistrationNativeSecretWordSource (ByteCache byteCache byteSource)
open PqxdhKemIndCca (MlKemSharedSecret)
variable {Value Observation : Type}
attribute [local irreducible] uniformSample

noncomputable def symbolicView (observe : MlKemSharedSecret → (Value × ByteCache) → Observation)
    (work : OracleComp Spec Value) : ProbComp Observation := do
  let candidate ← $ᵗ MlKemSharedSecret
  (fun result => observe candidate (result.1, byteCache candidate result.2)) <$>
    (simulateQ symbolic work).run ∅

noncomputable def bytesView (observe : MlKemSharedSecret → (Value × ByteCache) → Observation)
    (work : OracleComp Spec Value) : ProbComp Observation := do
  let candidate ← $ᵗ MlKemSharedSecret
  observe candidate <$> (simulateQ (byteSource candidate) work).run ∅

private theorem fixed_complete (candidate : MlKemSharedSecret) (work : OracleComp Spec Value) :
    discreteDistance ((simulateQ symbolic work).run ∅) ((simulateQ (actual candidate) work).run ∅) ≤
      (Pr{let result ← run work}[candidate ∈ result.2.2]).toReal := by
  have compared := RawCtxSelectedAliasCoupling.recorded_distance symbolic (actual candidate) literals candidate work (∅ : Cache)
  rw [RegistrationNativeSecretWord.actual_routed] at compared
  have mapped := (discreteDistance_map_le (Prod.map id Prod.fst) _ _).trans compared
  simpa only [RawCtxSelectedQueryTrace.complete, run] using mapped

private theorem complete_source (candidate : MlKemSharedSecret) (work : OracleComp Spec Value) :
    Prod.map id (byteCache candidate) <$> (simulateQ (actual candidate) work).run ∅ =
      (simulateQ (byteSource candidate) work).run ∅ := by
  have empty : byteCache candidate ∅ = ∅ := by
    apply QueryCache.ext
    intro bytes
    change (RegistrationNativeSecretWord.decode candidate bytes).bind (fun _ => none) = none
    cases RegistrationNativeSecretWord.decode candidate bytes <;> rfl
  simpa only [empty] using RegistrationNativeSecretWordSource.program_source candidate work ∅

private theorem fixed_observed (candidate : MlKemSharedSecret) (work : OracleComp Spec Value)
    (observe : (Value × Cache) → Observation) :
    discreteDistance (observe <$> (simulateQ symbolic work).run ∅)
      (observe <$> (simulateQ (actual candidate) work).run ∅) ≤
      (Pr{let result ← run work}[candidate ∈ result.2.2]).toReal :=
  (discreteDistance_map_le observe _ _).trans (fixed_complete candidate work)

attribute [local irreducible] byteCache symbolic actual run

private theorem normalized_close (observe : MlKemSharedSecret → (Value × Cache) → Observation)
    (work : OracleComp Spec Value) (cap : Nat) (bounded : work.IsQueryBoundP IsKey cap) :
    ENNReal.ofReal (discreteDistance
      (do let candidate ← $ᵗ MlKemSharedSecret; observe candidate <$> (simulateQ symbolic work).run ∅)
      (do let candidate ← $ᵗ MlKemSharedSecret; observe candidate <$> (simulateQ (actual candidate) work).run ∅)) ≤
      cap * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  have averaged := PqxdhExtractRomHiddenSuffix.tvDist_bind_le_probEvent ($ᵗ MlKemSharedSecret)
    (fun candidate => observe candidate <$> (simulateQ symbolic work).run ∅)
    (fun candidate => observe candidate <$> (simulateQ (actual candidate) work).run ∅)
    (fun _ => run work) (fun candidate result => candidate ∈ result.2.2)
    (fun candidate _ => fixed_observed candidate work (observe candidate))
  exact (ENNReal.ofReal_le_ofReal averaged).trans
    ((ENNReal.ofReal_toReal (prEvent_ne_top _)).le.trans (guess_bound work cap bounded))

/-- The full actual byte-table state and arbitrary candidate-dependent final observation retain the same single key-query loss. -/
theorem observed_close (observe : MlKemSharedSecret → (Value × ByteCache) → Observation)
    (work : OracleComp Spec Value) (cap : Nat) (bounded : work.IsQueryBoundP IsKey cap) :
    ENNReal.ofReal (discreteDistance (symbolicView observe work) (bytesView observe work)) ≤
      cap * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  have compared := normalized_close (fun candidate result => observe candidate (result.1, byteCache candidate result.2))
    work cap bounded
  have source : (do
      let candidate ← $ᵗ MlKemSharedSecret
      (fun result => observe candidate (result.1, byteCache candidate result.2)) <$>
        (simulateQ (actual candidate) work).run ∅) = bytesView observe work := by
    apply bind_congr
    intro candidate
    have projected := congrArg (Functor.map (observe candidate)) (complete_source candidate work)
    simpa only [Functor.map_map, Function.comp_def, Prod.map, id_eq] using projected
  rw [source] at compared
  exact compared

/-- Every event of the candidate, final native value and exact native cache inherits the coefficient-one bound. -/
theorem event_bound (observe : MlKemSharedSecret → (Value × ByteCache) → Observation)
    (work : OracleComp Spec Value) (cap : Nat) (bounded : work.IsQueryBoundP IsKey cap) (event : Observation → Prop) :
    Pr{let result ← bytesView observe work}[event result] ≤
      Pr{let result ← symbolicView observe work}[event result] + cap * (256 ^ 32 : ℝ≥0∞)⁻¹ := by
  have compared := prEvent_le_prEvent_add_ofReal_discreteDistance (bytesView observe work) (symbolicView observe work) event
  rw [discreteDistance_comm] at compared
  exact compared.trans (add_le_add le_rfl (observed_close observe work cap bounded))

end BeaconcryptCore.Computational.RegistrationNativeSecretWordCachedObservation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCachedObservation.observed_close' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCachedObservation.observed_close
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCachedObservation.event_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCachedObservation.event_bound

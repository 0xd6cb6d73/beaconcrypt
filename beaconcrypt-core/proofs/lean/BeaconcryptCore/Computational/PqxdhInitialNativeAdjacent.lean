import BeaconcryptCore.Computational.PqxdhInitialNativeRisk
import BeaconcryptCore.Computational.RawCtxAdjacentCacheNormalization

/-!
Both complete original builder/post stages share the same actual carried predecessor sampler. Only the earliest cached branch of the later stage is replaced by the original earlier-stage continuation, and its exact full-source collision probability is charged once. A common final observation still receives every original private state and source result. The fresh-child cryptographic comparison and its source freshness event remain separate consumers of this normalization.
-/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialNativeAdjacent
open PqxdhJointKdfGame PqxdhInitialNativeLog PqxdhInitialNativePrefix PqxdhInitialNativeCarried
open PqxdhInitialNativeRisk PqxdhInitialBeaconAmbient
variable {ι M P I D K X Response Shared Result Origin A N C : Type} {extra : OracleSpec ι} {S B : Nat}

abbrev Output (M P I D K Result Origin A N C : Type) (S B : Nat) :=
  Final M P I D K Result Origin S B × State A N C

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (execution : Execution extra M P I D K Result Origin S B)
  (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (Ambient A N C))

noncomputable def continued (stage : Nat) (cut : Carried extra M P I D K Result Origin A N C S B) :
    ProbComp (Output M P I D K Result Origin A N C S B) :=
  RawCtxPendingMixedPrefix.finish (handler source writer stage external)
    (RawCtxForwardScan.pack (PqxdhInitialOriginContext.frame mark sender route decode) cut)

noncomputable def run (stage : Nat) (state : State A N C) : ProbComp (Output M P I D K Result Origin A N C S B) :=
  (simulateQ (handler source writer stage external) (original source mark sender route decode execution)).run state

noncomputable def normalized (depth : Nat) (state : State A N C) : ProbComp (Output M P I D K Result Origin A N C S B) := by
  classical
  exact carried source writer mark sender route decode execution depth (depth + 1) external state >>= fun cut =>
    if Cached cut then continued source writer mark sender route decode external (depth + 1) cut
    else continued source writer mark sender route decode external (depth + 2) cut

/-- Both full adjacent source executions retain the same literal carried sampler and their complete original continuation and final state. -/
theorem source_adjacent (depth : Nat) (state : State A N C) (before : Depth depth state) :
    (carried source writer mark sender route decode execution depth (depth + 1) external state >>=
      continued source writer mark sender route decode external (depth + 1)) =
      run source writer mark sender route decode execution external (depth + 1) state ∧
    (carried source writer mark sender route decode execution depth (depth + 1) external state >>=
      continued source writer mark sender route decode external (depth + 2)) =
      run source writer mark sender route decode execution external (depth + 2) state := by
  constructor
  · exact carried_finish source writer mark sender route decode execution depth (depth + 1) external state
  · rw [carried_same source writer mark sender route decode execution depth external state before]
    exact carried_finish source writer mark sender route decode execution depth (depth + 2) external state

/-- Replacing only the original cached branch costs one actual chronological collision probability, bounded by the complete source schedule. -/
theorem normalization (depth k qPost : Nat)
    (bounded : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
    (state : State A N C) (valid : Valid depth k state) (clean : Clean state) :
    ENNReal.ofReal (tvDist
      (run source writer mark sender route decode execution external (depth + 2) state)
      (normalized source writer mark sender route decode execution external depth state)) ≤
      ∑ j ∈ Finset.range (7 + qPost * 67), ((k + j + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  classical
  rw [← (source_adjacent source writer mark sender route decode execution external depth state valid.2.1).2, normalized]
  exact (ofReal_tvDist_bind_left_event_le _ _ _ Cached (fun cut good => by simp only [good, ite_false])).trans
    ((VCVioLegacy.probEvent_eq_prEvent _ Cached).le.trans
      (cached_risk source writer mark sender route decode execution depth k qPost external bounded state valid clean))

/-- A common complete-state observation, including an appended private lineage check, preserves the one cached-branch charge. -/
theorem normalization_after {Observed : Type} (depth k qPost : Nat)
    (bounded : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
    (state : State A N C) (valid : Valid depth k state) (clean : Clean state)
    (observe : Output M P I D K Result Origin A N C S B → ProbComp Observed) :
    ENNReal.ofReal (tvDist
      (run source writer mark sender route decode execution external (depth + 2) state >>= observe)
      (normalized source writer mark sender route decode execution external depth state >>= observe)) ≤
      ∑ j ∈ Finset.range (7 + qPost * 67), ((k + j + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ :=
  (ENNReal.ofReal_le_ofReal (tvDist_bind_right_le observe _ _)).trans
    (normalization source writer mark sender route decode execution external depth k qPost bounded state valid clean)

/-- One unchanged final source decision pays its normalized fresh-child comparison and the derived cached-input sum with coefficient one. -/
theorem adjacent_bound (depth k qPost : Nat)
    (bounded : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
    (state : State A N C) (valid : Valid depth k state) (clean : Clean state)
    (observe : Output M P I D K Result Origin A N C S B → ProbComp Bool) :
    ENNReal.ofReal ((run source writer mark sender route decode execution external (depth + 1) state >>= observe).boolDistAdvantage
      (run source writer mark sender route decode execution external (depth + 2) state >>= observe)) ≤
      ENNReal.ofReal ((run source writer mark sender route decode execution external (depth + 1) state >>= observe).boolDistAdvantage
        (normalized source writer mark sender route decode execution external depth state >>= observe)) +
      ∑ j ∈ Finset.range (7 + qPost * 67), ((k + j + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  refine (ENNReal.ofReal_le_ofReal (ProbComp.boolDistAdvantage_triangle _
    (normalized source writer mark sender route decode execution external depth state >>= observe) _)).trans ?_
  simp only [ProbComp.boolDistAdvantage, VCVioLegacy.evalDist_singleton_eq_probOutput]
  rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  apply add_le_add le_rfl
  refine (ENNReal.ofReal_le_ofReal (abs_probOutput_toReal_sub_le_tvDist _ _)).trans ?_
  rw [tvDist_comm]
  exact normalization_after source writer mark sender route decode execution external depth k qPost bounded state valid clean observe

end BeaconcryptCore.Computational.PqxdhInitialNativeAdjacent

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeAdjacent.source_adjacent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeAdjacent.source_adjacent

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeAdjacent.normalization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeAdjacent.normalization

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeAdjacent.normalization_after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeAdjacent.normalization_after

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeAdjacent.adjacent_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeAdjacent.adjacent_bound

import BeaconcryptCore.Computational.RawCtxFirstParentRisk

/-!
Both original adjacent source games retain the same executable first-hit/predecessor sampler. Replacing only the random stage's earliest cached branch by the real stage's original continuation costs the source-derived chronological collision sum. Every other branch is unchanged, and the full original family, history, shared state, private cache, cursor and input log remain available to an arbitrary common continuation. This supplies the cached-branch term for the final same-event hybrid; it does not replace the fresh-child cryptographic comparison.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxAdjacentCacheNormalization
open PqxdhJointKdfGame RawCtxSelectiveFamilyLog RawCtxFirstParentRisk
variable {M P I D K A Result : Type} {S B : Nat}

abbrev Output (M P I D K A Result : Type) (S B : Nat) :=
  (Result × RawCtxProtocolReveals.State M P I D K S B) × LoggedState A

noncomputable def continued (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (stage : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (cut : RawCtxLoggedParentSampler.Cut M P I D K A Result S B) :
    ProbComp (Output M P I D K A Result S B) :=
  Prod.map (Prod.map id (RawCtxGenericFamilyLive.nativeState ConcreteRatchetKernel.mk)) id <$>
    RawCtxLoggedParentSampler.run source writer stage sender route decode cut

noncomputable def normalized (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A) :
    ProbComp (Output M P I D K A Result S B) := by
  classical
  exact RawCtxForwardParentSampler.first source writer depth (depth + 1) sender route decode client state initial >>=
    fun cut => if Cached cut then continued source writer (depth + 1) sender route decode cut
      else continued source writer (depth + 2) sender route decode cut

/-- Both full adjacent source games use the same actual forward sampler and preserve every original continuation and final private field. -/
theorem source_adjacent (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A)
    (before : initial.1.2.2.depth ≤ depth) :
    (RawCtxForwardParentSampler.first source writer depth (depth + 1) sender route decode client state initial >>=
      continued source writer (depth + 1) sender route decode) =
      family source writer (depth + 1) sender route decode client state initial.1.1 initial.1.2 initial.2 ∧
    (RawCtxForwardParentSampler.first source writer depth (depth + 1) sender route decode client state initial >>=
      continued source writer (depth + 2) sender route decode) =
      family source writer (depth + 2) sender route decode client state initial.1.1 initial.1.2 initial.2 := by
  have actual := RawCtxForwardParentSampler.first_adjacent source writer depth sender route decode client state initial before
  unfold continued
  simpa only [map_bind] using actual

/-- Replacing only the actual cached pending branch costs one original source collision probability, bounded here from the source S+51R budget. -/
theorem normalization (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth k : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A)
    (valid : Valid depth k initial) (clean : Clean initial) :
    ENNReal.ofReal (tvDist
      (family source writer (depth + 2) sender route decode client state initial.1.1 initial.1.2 initial.2)
      (normalized source writer depth sender route decode client state initial)) ≤
      ∑ j ∈ Finset.range (budget.1 .send + 51 * budget.1 .raw),
        ((k + j + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  classical
  rw [← (source_adjacent source writer depth sender route decode client state initial valid.2.1).2, normalized]
  exact (ofReal_tvDist_bind_left_event_le _ _ _ Cached (fun cut good => by simp only [good, ite_false])).trans
    (cached_risk source writer depth k sender route decode client budget bounded state initial valid clean)

/-- Any one common complete-state continuation, including a private appended lineage check, preserves the same cached-branch charge. -/
theorem normalization_after {Observed : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth k : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A)
    (valid : Valid depth k initial) (clean : Clean initial)
    (observe : Output M P I D K A Result S B → ProbComp Observed) :
    ENNReal.ofReal (tvDist
      (family source writer (depth + 2) sender route decode client state initial.1.1 initial.1.2 initial.2 >>= observe)
      (normalized source writer depth sender route decode client state initial >>= observe)) ≤
      ∑ j ∈ Finset.range (budget.1 .send + 51 * budget.1 .raw),
        ((k + j + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ :=
  (ENNReal.ofReal_le_ofReal (tvDist_bind_right_le observe _ _)).trans
    (normalization source writer depth k sender route decode client budget bounded state initial valid clean)

/-- The actual adjacent source advantage for one unchanged final decision is bounded by its collision-normalized comparison plus the derived chronological risk, with coefficient one. -/
theorem adjacent_bound (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (depth k : Nat) (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : RawCtxProtocolReveals.State M P I D K S B) (initial : LoggedState A)
    (valid : Valid depth k initial) (clean : Clean initial)
    (observe : Output M P I D K A Result S B → ProbComp Bool) :
    ENNReal.ofReal ((family source writer (depth + 1) sender route decode client state initial.1.1 initial.1.2 initial.2 >>= observe).boolDistAdvantage
      (family source writer (depth + 2) sender route decode client state initial.1.1 initial.1.2 initial.2 >>= observe)) ≤
      ENNReal.ofReal ((family source writer (depth + 1) sender route decode client state initial.1.1 initial.1.2 initial.2 >>= observe).boolDistAdvantage
        (normalized source writer depth sender route decode client state initial >>= observe)) +
      ∑ j ∈ Finset.range (budget.1 .send + 51 * budget.1 .raw),
        ((k + j + 1 : Nat) : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  let before : ProbComp Bool :=
    family source writer (depth + 1) sender route decode client state initial.1.1 initial.1.2 initial.2 >>= observe
  let after : ProbComp Bool :=
    family source writer (depth + 2) sender route decode client state initial.1.1 initial.1.2 initial.2 >>= observe
  let middle : ProbComp Bool := normalized source writer depth sender route decode client state initial >>= observe
  change ENNReal.ofReal (before.boolDistAdvantage after) ≤
    ENNReal.ofReal (before.boolDistAdvantage middle) + _
  refine (ENNReal.ofReal_le_ofReal (ProbComp.boolDistAdvantage_triangle before middle after)).trans ?_
  simp only [ProbComp.boolDistAdvantage, evalDist_apply_singleton]
  rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  apply add_le_add le_rfl
  refine (ENNReal.ofReal_le_ofReal (abs_probOutput_toReal_sub_le_tvDist middle after)).trans ?_
  rw [tvDist_comm]
  simpa only [after, middle] using
    normalization_after source writer depth k sender route decode client budget bounded state initial valid clean observe

end BeaconcryptCore.Computational.RawCtxAdjacentCacheNormalization

/-- info: 'BeaconcryptCore.Computational.RawCtxAdjacentCacheNormalization.source_adjacent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxAdjacentCacheNormalization.source_adjacent

/-- info: 'BeaconcryptCore.Computational.RawCtxAdjacentCacheNormalization.normalization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxAdjacentCacheNormalization.normalization

/-- info: 'BeaconcryptCore.Computational.RawCtxAdjacentCacheNormalization.normalization_after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxAdjacentCacheNormalization.normalization_after

/-- info: 'BeaconcryptCore.Computational.RawCtxAdjacentCacheNormalization.adjacent_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxAdjacentCacheNormalization.adjacent_bound

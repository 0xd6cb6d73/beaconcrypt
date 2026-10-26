import BeaconcryptCore.Computational.PqxdhInitialSampledParentSecrecy
import BeaconcryptCore.Computational.PqxdhInitialSourceLaterSecrecy
import BeaconcryptCore.Computational.RawCtxSupportedMixture

/-!
The complete preparation and shared64 initializer are retained in both source endpoints and the one constructed dependent main/tester reduction. Only the proved statistical source-simulation and cache terms are averaged. No primitive advantage is averaged or replaced by a selection over initializer responses.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSampledSourceEndpoints
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhInitialSourceInitialSecrecy PqxdhInitialSampledParent
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (depth remaining : Nat)
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)

noncomputable def localModel (random : Bool) (start : Start extra M P I D K X Response A N S B) : ProbComp Bool :=
  if random then PqxdhInitialSourcePreparedSecrecy.random source writer start.1.selectedMessage zeroRoot (response start) start.1.other
    sender route decode start.1.index start.1.metadata { start.1.ready with root := zeroRoot } start.1.post start.1.before
    start.1.selected start.1.number start.1.ancestors start.1.disclosed start.1.shared start.1.privateState start.1.cache depth remaining
  else PqxdhInitialSourcePreparedSecrecy.actual source writer start.1.selectedMessage zeroRoot (response start) start.1.other
    sender route decode start.1.index start.1.metadata { start.1.ready with root := zeroRoot } start.1.post start.1.before
    start.1.selected start.1.number start.1.ancestors start.1.disclosed start.1.shared start.1.privateState start.1.cache depth remaining

noncomputable def observation (random : Bool) (context : Context extra M P I D K X Response A N S B)
    (output : HmacBlock) : ProbComp Bool :=
  match context with
  | .inl decision => pure decision
  | .inr input => localModel source writer sender route decode depth remaining random (input, output)

noncomputable def mixture (random : Bool) (prior : ProbComp (Context extra M P I D K X Response A N S B)) : ProbComp Bool := do
  let context ← prior
  let output ← $ᵗ HmacBlock
  observation source writer sender route decode depth remaining random context output

variable (prior : ProbComp (Context extra M P I D K X Response A N S B))
local notation "sampler" => PqxdhInitialSampledParent.sample source writer sender route decode depth prior
local notation "address" => PqxdhInitialSampledParent.address source writer sender route decode depth
local notation "actualGame" => PqxdhInitialSampledParentSecrecy.actual source writer sender route decode depth remaining sampler address
local notation "randomGame" => PqxdhInitialSampledParentSecrecy.random source writer sender route decode depth remaining sampler address

/-- The real native observer is a single constructed reduction over the exact original preparation and shared initializer distribution. -/
theorem actual_mixture :
    𝒟[actualGame] = 𝒟[mixture source writer sender route decode depth remaining false prior] := by
  have erase := RawCtxSupportedSample.sum_run prior (fun context => ($ᵗ HmacBlock) >>=
    observation source writer sender route decode depth remaining false context)
  unfold PqxdhInitialSampledParentSecrecy.actual RawCtxSelectedParentCandidates.sample PqxdhInitialSampledParent.sample
  simp only [bind_assoc]
  calc
    _ = 𝒟[RawCtxSupportedSample.sum prior >>= fun context => ($ᵗ HmacBlock) >>=
      observation source writer sender route decode depth remaining false (Sum.map id Subtype.val context)] := by
      apply EvalDistEq.evalDist_eq
      refine EvalDistEq.bind_right (RawCtxSupportedSample.sum prior) fun context => ?_
      refine EvalDistEq.bind_right ($ᵗ HmacBlock) fun output => ?_
      cases context with
      | inl decision =>
        simp only [pure_bind, PqxdhInitialSampledParent.native, observation, Sum.map_inl, id_eq]
        exact OracleComp.EvalDistEq.bind_const ($ᵗ FullOutput) (pure decision)
      | inr input =>
        simp only [bind_assoc, pure_bind, Sum.map_inr, observation, localModel, Bool.false_eq_true, ite_false,
          PqxdhInitialSampledParent.native, PqxdhInitialSampledParent.address]
        simp only [PqxdhInitialSourcePreparedSecrecy.actual, PqxdhInitialCommonSecrecy.actual,
          RawCtxSelectedParentCandidates.sample, bind_assoc, pure_bind]
        rfl
    _ = _ := congrArg evalDist erase

/-- The independent-child native observer is a single constructed reduction over the exact original preparation and shared initializer distribution. -/
theorem random_mixture :
    𝒟[randomGame] = 𝒟[mixture source writer sender route decode depth remaining true prior] := by
  have erase := RawCtxSupportedSample.sum_run prior (fun context => ($ᵗ HmacBlock) >>=
    observation source writer sender route decode depth remaining true context)
  unfold PqxdhInitialSampledParentSecrecy.random RawCtxSelectedParentCandidates.sample PqxdhInitialSampledParent.sample
  simp only [bind_assoc]
  calc
    _ = 𝒟[RawCtxSupportedSample.sum prior >>= fun context => ($ᵗ HmacBlock) >>=
      observation source writer sender route decode depth remaining true (Sum.map id Subtype.val context)] := by
      apply EvalDistEq.evalDist_eq
      refine EvalDistEq.bind_right (RawCtxSupportedSample.sum prior) fun context => ?_
      refine EvalDistEq.bind_right ($ᵗ HmacBlock) fun output => ?_
      cases context with
      | inl decision =>
        simp only [pure_bind, PqxdhInitialSampledParent.native, observation, Sum.map_inl, id_eq]
        exact (OracleComp.EvalDistEq.bind_const ($ᵗ FullOutput) _).trans
          (OracleComp.EvalDistEq.bind_const ($ᵗ FullOutput) (pure decision))
      | inr input =>
        simp only [bind_assoc, pure_bind, Sum.map_inr, observation, localModel, ite_true,
          PqxdhInitialSampledParent.native, PqxdhInitialSampledParent.address]
        simp only [PqxdhInitialSourcePreparedSecrecy.random, PqxdhInitialCommonSecrecy.random,
          RawCtxSelectedParentCandidates.sample, bind_assoc, pure_bind]
        rfl
    _ = _ := congrArg evalDist erase

/-- For every supported preparation and complete initial64 response, the real source endpoint pays only its actual prior-input collision probability bound. -/
theorem local_real (start : Start extra M P I D K X Response A N S B) (qPost : Nat)
    (bounded : ∀ reply, (start.1.post reply).IsTotalQueryBound qPost)
    (position : start.1.number.val = (depth + 1) + remaining + 1) :
    ENNReal.ofReal ((sourceGame source writer sender route decode start.1 zeroRoot (response start) (depth + 1)).boolDistance
      (localModel source writer sender route decode depth remaining false start)) ≤
      ((8 + qPost * 67 : Nat) : ENNReal) * (2 ^ 256 : ENNReal)⁻¹ := by
  have compared := PqxdhInitialSourceLaterMixture.real_bound source writer start.1.selectedMessage zeroRoot (response start) start.1.other
    sender route decode start.1.index start.1.metadata { start.1.ready with root := zeroRoot } start.1.post start.1.before
    start.1.selected start.1.number start.1.ancestors start.1.disclosed start.1.shared start.1.privateState start.1.cache depth remaining position
  have collision := PqxdhInitialSourceLaterMixture.collision_bound source writer start.1.selectedMessage zeroRoot (response start) start.1.other
    sender route decode start.1.index start.1.metadata { start.1.ready with root := zeroRoot } start.1.post start.1.before
    start.1.selected start.1.number start.1.ancestors start.1.disclosed start.1.shared start.1.privateState start.1.cache depth qPost bounded
  have same := PqxdhInitialSourceLaterMixture.resumed_real source writer start.1.selectedMessage zeroRoot (response start) start.1.other
    sender route decode start.1.index start.1.metadata { start.1.ready with root := zeroRoot } start.1.post start.1.before
    start.1.selected start.1.number start.1.ancestors start.1.disclosed start.1.shared start.1.privateState start.1.cache depth
  simpa only [ProbComp.boolDistance, congrArg (fun μ : MeasureTheory.Measure Bool => μ {true}) same, sourceGame, localModel, Bool.false_eq_true, ite_false] using
    compared.trans collision

/-- Averaging the exact real source endpoint over the original preparation and shared initial64 draw retains its one collision allowance without a target-response selection factor. -/
theorem real_bound (qPost : Nat)
    (bounded : ∀ input, Sum.inr input ∈ support prior → ∀ reply, (input.post reply).IsTotalQueryBound qPost)
    (position : ∀ input, Sum.inr input ∈ support prior → input.number.val = (depth + 1) + remaining + 1) :
    ENNReal.ofReal ((PqxdhInitialSourceSampled.game source writer sender route decode prior (depth + 1)).boolDistance actualGame) ≤
      ((8 + qPost * 67 : Nat) : ENNReal) * (2 ^ 256 : ENNReal)⁻¹ := by
  have mixed : ENNReal.ofReal ((PqxdhInitialSourceSampled.game source writer sender route decode prior (depth + 1)).boolDistance
      (mixture source writer sender route decode depth remaining false prior)) ≤
      ((8 + qPost * 67 : Nat) : ENNReal) * (2 ^ 256 : ENNReal)⁻¹ := by
    apply RawCtxSupportedMixture.bound prior
    intro context supported
    apply RawCtxSupportedMixture.bound ($ᵗ HmacBlock)
    intro output _
    cases context with
    | inl decision => simp only [PqxdhInitialSourceSampled.observe, observation, ProbComp.boolDistance, sub_self, abs_zero,
        ENNReal.ofReal_zero, zero_le]
    | inr input =>
      exact local_real source writer sender route decode depth remaining (input, output) qPost
        (bounded input supported) (position input supported)
  have same := actual_mixture source writer sender route decode depth remaining prior
  simpa only [ProbComp.boolDistance, congrArg (fun μ : MeasureTheory.Measure Bool => μ {true}) same] using mixed

/-- The actual later source endpoint pays its single prior-input collision allowance and the complete cached-prefix normalization sum. -/
theorem local_random (start : Start extra M P I D K X Response A N S B) (qPost : Nat)
    (bounded : ∀ reply, (start.1.post reply).IsTotalQueryBound qPost)
    (position : start.1.number.val = (depth + 1) + remaining + 1) :
    ENNReal.ofReal ((sourceGame source writer sender route decode start.1 zeroRoot (response start) (depth + 2)).boolDistance
      (localModel source writer sender route decode depth remaining true start)) ≤
      ((8 + qPost * 67 : Nat) : ENNReal) * (2 ^ 256 : ENNReal)⁻¹ +
        ∑ j ∈ Finset.range (7 + qPost * 67), ((j + 1 : Nat) : ENNReal) * (2 ^ 256 : ENNReal)⁻¹ := by
  let normalized := PqxdhInitialNativeAdjacent.normalized source writer (marker source start) sender route decode
    (PqxdhInitialSourceExperiment.execution (response start) start.1.index start.1.metadata { start.1.ready with root := zeroRoot }
      start.1.post start.1.before)
    (PqxdhInitialOriginFinishPath.withInitial source start.1.selectedMessage zeroRoot (response start) start.1.other) depth
    (PqxdhInitialSourceExperiment.initialState (PqxdhInitialSourceExperiment.root source zeroRoot (response start) start.1.selected)
      start.1.shared start.1.privateState start.1.cache) >>=
      PqxdhInitialSourcePreparedSecrecy.observe source zeroRoot (response start) start.1.selected start.1.number start.1.ancestors start.1.disclosed
  have compared := PqxdhInitialSourceLaterMixture.random_bound source writer start.1.selectedMessage zeroRoot (response start) start.1.other
    sender route decode start.1.index start.1.metadata { start.1.ready with root := zeroRoot } start.1.post start.1.before
    start.1.selected start.1.number start.1.ancestors start.1.disclosed start.1.shared start.1.privateState start.1.cache depth remaining position
  have collision := PqxdhInitialSourceLaterMixture.collision_bound source writer start.1.selectedMessage zeroRoot (response start) start.1.other
    sender route decode start.1.index start.1.metadata { start.1.ready with root := zeroRoot } start.1.post start.1.before
    start.1.selected start.1.number start.1.ancestors start.1.disclosed start.1.shared start.1.privateState start.1.cache depth qPost bounded
  have same := PqxdhInitialSourceLaterMixture.resumed_normalized source writer start.1.selectedMessage zeroRoot (response start) start.1.other
    sender route decode start.1.index start.1.metadata { start.1.ready with root := zeroRoot } start.1.post start.1.before
    start.1.selected start.1.number start.1.ancestors start.1.disclosed start.1.shared start.1.privateState start.1.cache depth
  have back : ENNReal.ofReal (normalized.boolDistance (localModel source writer sender route decode depth remaining true start)) ≤
      ((8 + qPost * 67 : Nat) : ENNReal) * (2 ^ 256 : ENNReal)⁻¹ := by
    simpa only [ProbComp.boolDistance, congrArg (fun μ : MeasureTheory.Measure Bool => μ {true}) same, normalized, marker, localModel, ite_true] using compared.trans collision
  have normal := PqxdhInitialSourceExperiment.normalization source writer start.1.selectedMessage zeroRoot (response start) start.1.other
    sender route decode start.1.index start.1.metadata { start.1.ready with root := zeroRoot } start.1.post start.1.before
    start.1.selected start.1.number start.1.ancestors start.1.disclosed start.1.shared start.1.privateState start.1.cache depth qPost bounded
  have front : ENNReal.ofReal ((sourceGame source writer sender route decode start.1 zeroRoot (response start) (depth + 2)).boolDistance normalized) ≤
      ∑ j ∈ Finset.range (7 + qPost * 67), ((j + 1 : Nat) : ENNReal) * (2 ^ 256 : ENNReal)⁻¹ := by
    simpa only [ProbComp.boolDistance, ← prEvent_eq_evalDist_singleton] using
      (ENNReal.ofReal_le_ofReal (abs_prEvent_toReal_sub_le_discreteDistance
        (sourceGame source writer sender route decode start.1 zeroRoot (response start) (depth + 2)) normalized)).trans normal
  have triangle := ENNReal.ofReal_le_ofReal (ProbComp.boolDistance_triangle
    (sourceGame source writer sender route decode start.1 zeroRoot (response start) (depth + 2)) normalized
    (localModel source writer sender route decode depth remaining true start))
  simp only [ProbComp.boolDistance] at triangle
  rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)] at triangle
  simpa only [ProbComp.boolDistance, add_comm] using triangle.trans (add_le_add front back)

/-- The later native reduction observer is connected to the same complete sampled source experiment, retaining the actual source normalization and collision terms with no initializer-selection loss. -/
theorem random_bound (qPost : Nat)
    (bounded : ∀ input, Sum.inr input ∈ support prior → ∀ reply, (input.post reply).IsTotalQueryBound qPost)
    (position : ∀ input, Sum.inr input ∈ support prior → input.number.val = (depth + 1) + remaining + 1) :
    ENNReal.ofReal ((PqxdhInitialSourceSampled.game source writer sender route decode prior (depth + 2)).boolDistance randomGame) ≤
      ((8 + qPost * 67 : Nat) : ENNReal) * (2 ^ 256 : ENNReal)⁻¹ +
        ∑ j ∈ Finset.range (7 + qPost * 67), ((j + 1 : Nat) : ENNReal) * (2 ^ 256 : ENNReal)⁻¹ := by
  have mixed : ENNReal.ofReal ((PqxdhInitialSourceSampled.game source writer sender route decode prior (depth + 2)).boolDistance
      (mixture source writer sender route decode depth remaining true prior)) ≤
      ((8 + qPost * 67 : Nat) : ENNReal) * (2 ^ 256 : ENNReal)⁻¹ +
        ∑ j ∈ Finset.range (7 + qPost * 67), ((j + 1 : Nat) : ENNReal) * (2 ^ 256 : ENNReal)⁻¹ := by
    apply RawCtxSupportedMixture.bound prior
    intro context supported
    apply RawCtxSupportedMixture.bound ($ᵗ HmacBlock)
    intro output _
    cases context with
    | inl decision => simp only [PqxdhInitialSourceSampled.observe, observation, ProbComp.boolDistance, sub_self, abs_zero,
        ENNReal.ofReal_zero, zero_le]
    | inr input =>
      exact local_random source writer sender route decode depth remaining (input, output) qPost
        (bounded input supported) (position input supported)
  have same := random_mixture source writer sender route decode depth remaining prior
  simpa only [ProbComp.boolDistance, congrArg (fun μ : MeasureTheory.Measure Bool => μ {true}) same] using mixed

end BeaconcryptCore.Computational.PqxdhInitialSampledSourceEndpoints

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSampledSourceEndpoints.actual_mixture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSampledSourceEndpoints.actual_mixture
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSampledSourceEndpoints.random_mixture' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSampledSourceEndpoints.random_mixture
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSampledSourceEndpoints.local_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSampledSourceEndpoints.local_real
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSampledSourceEndpoints.real_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSampledSourceEndpoints.real_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSampledSourceEndpoints.local_random' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSampledSourceEndpoints.local_random
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSampledSourceEndpoints.random_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSampledSourceEndpoints.random_bound

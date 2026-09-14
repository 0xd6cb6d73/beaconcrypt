import BeaconcryptCore.Computational.RawCtxSelectedInputCandidates

/-!
A separately constructed full-output distinguisher tests whether any actual public candidate evaluation reproduces the supplied child output. The hidden input is retained only by the private winning event, never passed to this tester. For an independently uniform 76-byte child, acceptance implies membership in the complete image of the fixed 32-byte-input function, whose probability is at most 2^-352 even if the candidate list is chosen adaptively after seeing the child.

The real-child membership event is therefore bounded by the actual joint-sampler full-output Extract and ordinary two-query HMAC PRF advantages plus this image term. This is a separate reduction from an independent-input guessing bound; no real-child independence is asserted. Public HKDF remains fixed and real, with at most one instrumented full evaluation per returned candidate. The source sampler and complete observer must still be instantiated by the reached protocol execution and their own budgets. No freshness, source reachability, initial-output sampler, global hybrid, or small primitive advantage is assumed by this generic endpoint. Snapshots, persistence and restoration are excluded.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxFullPreimageTester
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf

def test (function : RootOutput → FullOutput) (output : FullOutput) (candidates : List RootOutput) : Bool :=
  candidates.any (fun candidate => decide (function candidate = output))

/-- The tester compares only public candidate evaluations with the supplied full output. -/
theorem test_iff (function : RootOutput → FullOutput) (output : FullOutput) (candidates : List RootOutput) :
    test function output candidates = true ↔ ∃ candidate ∈ candidates, function candidate = output := by
  simp [test, List.any_eq_true]

/-- Even adaptively chosen candidates can accept only outputs in the fixed function's finite image. -/
theorem uniform_image (function : RootOutput → FullOutput) :
    Pr[fun output => output ∈ Set.range function | $ᵗ FullOutput] ≤
      (Fintype.card RootOutput : ENNReal) / (Fintype.card FullOutput : ENNReal) := by
  classical
  rw [probEvent_uniformSample]
  have image : Finset.univ.filter (fun output => output ∈ Set.range function) =
      Finset.univ.image function := by ext output; simp
  rw [image]
  exact ENNReal.div_le_div_right (by exact_mod_cast Finset.card_image_le (s := Finset.univ) (f := function)) _

/-- A full 76-byte output has exactly 608 bits. -/
theorem full_card : Fintype.card FullOutput = 2 ^ 608 := by
  rw [card_vector]
  have byteCard : Fintype.card UInt8 = 256 := by
    set_option maxRecDepth 100000 in rfl
  rw [byteCard]
  calc
    256 ^ 76 = (2 ^ 8) ^ 76 := by norm_num
    _ = 2 ^ (8 * 76) := by rw [pow_mul]
    _ = 2 ^ 608 := by norm_num

/-- The complete fixed 32-byte input image occupies at most a 2^-352 fraction of uniform full 76-byte outputs. -/
theorem uniform_image352 (function : RootOutput → FullOutput) :
    Pr[fun output => output ∈ Set.range function | $ᵗ FullOutput] ≤
      (2 ^ 352 : ENNReal)⁻¹ := by
  convert uniform_image function using 1
  rw [PqxdhMaterialKeyCollisions.material_key_card, full_card]
  have cancellation := ENNReal.mul_div_mul_left (c := (2 : ENNReal) ^ 256) 1 ((2 : ENNReal) ^ 352)
    (by simp) (by simp)
  simpa only [Nat.cast_pow, Nat.cast_ofNat, show 608 = 256 + 352 from rfl,
    pow_add, Nat.cast_mul, mul_one, one_div] using cancellation.symm

/-- This complete observer receives context and full output, then tests only the candidates returned by the original continuation. -/
noncomputable def tester {Context Result : Type} (function : RootOutput → FullOutput)
    (observe : Context → FullOutput → ProbComp Result) (candidates : Result → List RootOutput) : FullObserver Context :=
  fun context output => (fun result => test function output (candidates result)) <$> observe context output

/-- The complete adaptive observer cannot cause acceptance outside the fixed input image. -/
theorem uniform_tester {Context Result : Type} (function : RootOutput → FullOutput)
    (observe : Context → FullOutput → ProbComp Result) (candidates : Result → List RootOutput) (context : Context) :
    Pr[= true | ($ᵗ FullOutput) >>= tester function observe candidates context] ≤ (2 ^ 352 : ENNReal)⁻¹ := by
  rw [← probEvent_eq_eq_probOutput']
  refine (probEvent_bind_le_probEvent (p := fun output => output ∈ Set.range function) ?_).trans (uniform_image352 function)
  intro output _ absent
  rw [tester, probEvent_map]
  apply probEvent_eq_zero_iff.mpr
  intro result _ accepted
  obtain ⟨candidate, _, same⟩ := (test_iff function output (candidates result)).mp accepted.symm
  exact absent ⟨candidate, same⟩

/-- The private event retains the actual target solely for the experiment's final event. -/
def actual {Context Result : Type} (function : RootOutput → FullOutput)
    (sample : ProbComp (Context × RootOutput)) (observe : Context → FullOutput → ProbComp Result) :
    ProbComp (RootOutput × Result) := do
  let (context, target) ← sample
  (fun result => (target, result)) <$> observe context (function target)

/-- The endpoint's input is exactly the sampled 32-byte vector, serialized without changing context. -/
def byteSampler {Context : Type} (sample : ProbComp (Context × RootOutput)) : SecretInputSampler Context :=
  ((fun pair : Context × RootOutput => (pair.1, pair.2.toList)) <$> sample : ProbComp (Context × Pqxdh.Bytes))

/-- A real target in the returned candidates always makes the target-free tester accept. -/
theorem actual_test {Context Result : Type} (function : RootOutput → FullOutput)
    (sample : ProbComp (Context × RootOutput)) (observe : Context → FullOutput → ProbComp Result)
    (candidates : Result → List RootOutput) :
    Pr[fun pair => pair.1 ∈ candidates pair.2 | actual function sample observe] ≤
      Pr[= true | sample >>= fun pair => tester function observe candidates pair.1 (function pair.2)] := by
  rw [actual, probEvent_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun pair => mul_le_mul' le_rfl ?_
  rw [probEvent_map, ← probEvent_eq_eq_probOutput', tester, probEvent_map]
  exact probEvent_mono'' fun result member =>
    ((test_iff function (function pair.2) (candidates result)).mpr ⟨pair.2, member, rfl⟩).symm

/-- The complete sampler precedes the independently uniform child, with no restriction on subsequent adaptive candidates. -/
theorem independent_test {Context Result : Type} (function : RootOutput → FullOutput)
    (sample : SecretInputSampler Context) (observe : Context → FullOutput → ProbComp Result)
    (candidates : Result → List RootOutput) :
    Pr[= true | independentFullGame sample (tester function observe candidates)] ≤ (2 ^ 352 : ENNReal)⁻¹ := by
  rw [← probEvent_eq_eq_probOutput', independentFullGame]
  exact probEvent_bind_le_of_forall_le fun pair _ => by
    simpa only [probEvent_eq_eq_probOutput'] using uniform_tester function observe candidates pair.1

/-- Every tester evaluation uses the actual public fixed HKDF at the ratchet label. -/
def production (source : FixedHkdfSha512NoSaltSource) (input : RootOutput) : FullOutput :=
  PqxdhJointKdf.productionStream source.crypto (FixedHkdfDomain.ratchet.address input.toList)

/-- Serialization preserves the exact source tester computation, including the complete continuation. -/
theorem source_test {Context Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp (Context × RootOutput)) (observe : Context → FullOutput → ProbComp Result)
    (candidates : Result → List RootOutput) :
    sourceFullGame source .ratchet (byteSampler sample) (tester (production source) observe candidates) =
      sample >>= fun pair => tester (production source) observe candidates pair.1 (production source pair.2) := by
  simp only [sourceFullGame, byteSampler, bind_map_left, production]

/-- Real-child target recovery is bounded by a separately constructed full-output Extract/PRF tester and the finite-image term. -/
theorem source_alias_bound {Context Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (sample : ProbComp (Context × RootOutput)) (observe : Context → FullOutput → ProbComp Result)
    (candidates : Result → List RootOutput) :
    Pr[fun pair => pair.1 ∈ candidates pair.2 | actual (production source) sample observe] ≤
      (2 ^ 352 : ENNReal)⁻¹ + ENNReal.ofReal (
        (extractRealGame hmac (byteSampler sample)
          (fullExtractReduction hmac .ratchet (tester (production source) observe candidates))).boolDistAdvantage
        (extractUniformGame (byteSampler sample)
          (fullExtractReduction hmac .ratchet (tester (production source) observe candidates))) +
        (hmacPrfRealGame hmac (fullExpandReduction .ratchet (byteSampler sample)
          (tester (production source) observe candidates))).boolDistAdvantage
        (hmacPrfRandomGame (fullExpandReduction .ratchet (byteSampler sample)
          (tester (production source) observe candidates)))) := by
  have actualBound := actual_test (production source) sample observe candidates
  rw [← source_test] at actualBound
  refine actualBound.trans ((ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage _
    (independentFullGame (byteSampler sample) (tester (production source) observe candidates))).trans ?_)
  exact add_le_add (independent_test (production source) (byteSampler sample) observe candidates)
    (ENNReal.ofReal_le_ofReal (sourceFullAdvantage_le_extract_add_hmac source hmac correct .ratchet
      (byteSampler sample) (tester (production source) observe candidates)))

/-- Instrumentation for the tester's local real function evaluations. -/
abbrev EvaluationSpec := RootOutput →ₒ FullOutput

def evaluate (output : FullOutput) : List RootOutput → OracleComp EvaluationSpec Bool
  | [] => pure false
  | candidate :: rest => do
      let value ← EvaluationSpec.query candidate
      if value = output then pure true else evaluate output rest

def realEvaluation (function : RootOutput → FullOutput) : QueryImpl EvaluationSpec ProbComp :=
  fun candidate => pure (function candidate)

/-- The instrumented tester is the same real public computation; it does not replace public HKDF by a random oracle. -/
theorem evaluate_real (function : RootOutput → FullOutput) (output : FullOutput) (candidates : List RootOutput) :
    simulateQ (realEvaluation function) (evaluate output candidates) = pure (test function output candidates) := by
  induction candidates with
  | nil => rfl
  | cons candidate rest ih =>
    simp only [evaluate, simulateQ_bind, simulateQ_spec_query, realEvaluation, pure_bind]
    split <;> simp_all [test]

/-- Every possible evaluation reply is counted, including repeats; at most one real full HKDF evaluation per candidate is needed. -/
theorem evaluate_queries (output : FullOutput) (candidates : List RootOutput) :
    (evaluate output candidates).IsTotalQueryBound candidates.length := by
  induction candidates with
  | nil => trivial
  | cons candidate rest ih =>
    simp only [evaluate, isTotalQueryBound_query_bind_iff, List.length_cons, Nat.add_sub_cancel]
    exact ⟨by omega, fun value => by split <;> trivial⟩

/-- The tester retains every uniform call made by the supplied observer, adding no uniform sampling of its own. -/
theorem tester_uniform {Context Result : Type} (function : RootOutput → FullOutput)
    (observe : Context → FullOutput → ProbComp Result) (candidates : Result → List RootOutput)
    {budget : Nat} (bounded : ∀ context output, (observe context output).IsTotalQueryBound budget) :
    ∀ context output, (tester function observe candidates context output).IsTotalQueryBound budget := by
  intro context output
  exact (isQueryBound_map_iff _ _ _ _ _).mpr (bounded context output)

/-- Serializing the actual vector sampler preserves its complete uniform-call budget. -/
theorem byteSampler_uniform {Context : Type} (sample : ProbComp (Context × RootOutput))
    {budget : Nat} (bounded : sample.IsTotalQueryBound budget) :
    (byteSampler sample).IsTotalQueryBound budget := by
  exact (isQueryBound_map_iff _ _ _ _ _).mpr bounded

/-- Instrumenting each candidate evaluation preserves the complete observer and its exact Boolean answer. -/
theorem tester_evaluated {Context Result : Type} (function : RootOutput → FullOutput)
    (observe : Context → FullOutput → ProbComp Result) (candidates : Result → List RootOutput)
    (context : Context) (output : FullOutput) :
    tester function observe candidates context output =
      observe context output >>= fun result => simulateQ (realEvaluation function) (evaluate output (candidates result)) := by
  simp only [evaluate_real, bind_pure_comp, tester]

/-- The complete tester adds at most the supplied supported candidate count in real full-output evaluations. -/
theorem tester_evaluation_bound {Context Result : Type}
    (observe : Context → FullOutput → ProbComp Result) (candidates : Result → List RootOutput)
    {budget : Nat}
    (bounded : ∀ context output result, result ∈ support (observe context output) → (candidates result).length ≤ budget) :
    ∀ context output result, result ∈ support (observe context output) →
      (evaluate output (candidates result)).IsTotalQueryBound budget := by
  intro context output result supported
  exact (evaluate_queries output (candidates result)).mono (bounded context output result supported)

/-- The separately constructed PRF reduction uses at most two ordinary HMAC challenge queries and retains every sampler/observer uniform call. -/
theorem reduction_bounds {Context Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp (Context × RootOutput)) (observe : Context → FullOutput → ProbComp Result)
    (candidates : Result → List RootOutput) (qSample qObserve : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observeBound : ∀ context output, (observe context output).IsTotalQueryBound qObserve) :
    (fullExpandReduction .ratchet (byteSampler sample) (tester (production source) observe candidates)).IsQueryBoundP
        IsHmacChallengeQuery 2 ∧
    (fullExpandReduction .ratchet (byteSampler sample) (tester (production source) observe candidates)).IsQueryBoundP
        PqxdhFullSecretInputKdf.IsHmacUniformQuery (qSample + qObserve) := by
  exact ⟨fullExpandReduction_hmac_query_bound _ _ _,
    fullExpandReduction_uniform_query_bound _ _ _ (byteSampler_uniform sample sampleBound)
      (tester_uniform _ _ _ observeBound)⟩

/-- The actual target-bearing experiment charges its complete sampler and original continuation without using a distributional cost transport. -/
theorem actual_uniform {Context Result : Type} (function : RootOutput → FullOutput)
    (sample : ProbComp (Context × RootOutput)) (observe : Context → FullOutput → ProbComp Result)
    (qSample qObserve : Nat) (sampleBound : sample.IsTotalQueryBound qSample)
    (observeBound : ∀ context output, (observe context output).IsTotalQueryBound qObserve) :
    (actual function sample observe).IsTotalQueryBound (qSample + qObserve) := by
  exact isTotalQueryBound_bind sampleBound fun pair =>
    (isQueryBound_map_iff _ _ _ _ _).mpr (observeBound pair.1 (function pair.2))

set_option maxRecDepth 2048 in
/-- All six source/challenger executions retain the same sampler and observer, and charge each complete challenger sample separately. -/
theorem challenger_bounds {Context Result : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (sample : ProbComp (Context × RootOutput)) (observe : Context → FullOutput → ProbComp Result)
    (candidates : Result → List RootOutput) (qSample qObserve : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observeBound : ∀ context output, (observe context output).IsTotalQueryBound qObserve) :
    (sourceFullGame source .ratchet (byteSampler sample) (tester (production source) observe candidates)).IsTotalQueryBound
        (qSample + qObserve) ∧
    (extractRealGame hmac (byteSampler sample)
      (fullExtractReduction hmac .ratchet (tester (production source) observe candidates))).IsTotalQueryBound
        (qSample + qObserve) ∧
    (extractUniformGame (byteSampler sample)
      (fullExtractReduction hmac .ratchet (tester (production source) observe candidates))).IsTotalQueryBound
        (qSample + (64 + qObserve)) ∧
    (hmacPrfRealGame hmac (fullExpandReduction .ratchet (byteSampler sample)
      (tester (production source) observe candidates))).IsTotalQueryBound (64 + (qSample + qObserve)) ∧
    (hmacPrfRandomGame (fullExpandReduction .ratchet (byteSampler sample)
      (tester (production source) observe candidates))).IsTotalQueryBound (qSample + (64 + (64 + qObserve))) ∧
    (independentFullGame (byteSampler sample) (tester (production source) observe candidates)).IsTotalQueryBound
        (qSample + (76 + qObserve)) := by
  have sampler := byteSampler_uniform sample sampleBound
  have observer := tester_uniform (production source) observe candidates observeBound
  refine ⟨sourceFullGame_uniform_query_bound source .ratchet _ _ sampler observer, ?_,
    fullExtractUniform_uniform_query_bound hmac .ratchet _ _ sampler observer,
    fullHmacReal_uniform_query_bound hmac .ratchet _ _ sampler observer,
    fullHmacRandom_uniform_query_bound .ratchet _ _ sampler observer,
    independentFullGame_uniform_query_bound _ _ sampler observer⟩
  exact isTotalQueryBound_bind sampler (fun pair => observer pair.1 _)

end BeaconcryptCore.Computational.RawCtxFullPreimageTester

/-- info: 'BeaconcryptCore.Computational.RawCtxFullPreimageTester.test_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFullPreimageTester.test_iff

/-- info: 'BeaconcryptCore.Computational.RawCtxFullPreimageTester.uniform_image' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFullPreimageTester.uniform_image

/-- info: 'BeaconcryptCore.Computational.RawCtxFullPreimageTester.full_card' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFullPreimageTester.full_card

/-- info: 'BeaconcryptCore.Computational.RawCtxFullPreimageTester.uniform_image352' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFullPreimageTester.uniform_image352

/-- info: 'BeaconcryptCore.Computational.RawCtxFullPreimageTester.uniform_tester' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFullPreimageTester.uniform_tester

/-- info: 'BeaconcryptCore.Computational.RawCtxFullPreimageTester.actual_test' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFullPreimageTester.actual_test

/-- info: 'BeaconcryptCore.Computational.RawCtxFullPreimageTester.independent_test' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFullPreimageTester.independent_test

/-- info: 'BeaconcryptCore.Computational.RawCtxFullPreimageTester.source_test' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFullPreimageTester.source_test

/-- info: 'BeaconcryptCore.Computational.RawCtxFullPreimageTester.source_alias_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFullPreimageTester.source_alias_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxFullPreimageTester.evaluate_real' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFullPreimageTester.evaluate_real

/-- info: 'BeaconcryptCore.Computational.RawCtxFullPreimageTester.evaluate_queries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFullPreimageTester.evaluate_queries

/-- info: 'BeaconcryptCore.Computational.RawCtxFullPreimageTester.tester_uniform' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFullPreimageTester.tester_uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxFullPreimageTester.byteSampler_uniform' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFullPreimageTester.byteSampler_uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxFullPreimageTester.tester_evaluated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFullPreimageTester.tester_evaluated

/-- info: 'BeaconcryptCore.Computational.RawCtxFullPreimageTester.tester_evaluation_bound' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFullPreimageTester.tester_evaluation_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxFullPreimageTester.reduction_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFullPreimageTester.reduction_bounds

/-- info: 'BeaconcryptCore.Computational.RawCtxFullPreimageTester.actual_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFullPreimageTester.actual_uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxFullPreimageTester.challenger_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFullPreimageTester.challenger_bounds

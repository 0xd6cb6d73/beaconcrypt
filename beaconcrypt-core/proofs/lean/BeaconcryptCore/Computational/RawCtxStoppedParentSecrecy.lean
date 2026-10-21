import BeaconcryptCore.Computational.RawCtxCheckedParentSecrecy

/-!
A stopped source execution either already computes its original final decision or retains one actual pending continuation. The common branch returns that same bit in every game and contributes no candidate; it is neither rejected nor conditioned away. The exact original sampler still precedes a paid full predecessor draw, and the random child game retains its paid full child draw even on common branches. Only pending branches invoke the existing checked family continuation.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxStoppedParentSecrecy
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxSelectedParentEntry
variable {Context M P I D K A : Type} {S B : Nat}

abbrev Trace (M P I D K A : Type) (S B : Nat) :=
  Bool ⊕ RawCtxSelectedParentHop.Trace A
    ((Bool × RawCtxFamilySourceFreshness.State M P I D K S B) × List RawCtxSelectedChain.Slot)

noncomputable def native (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : RawCtxCheckedParentSecrecy.Continuation Context M P I D K A S B)
    (context : (Bool ⊕ Context) × Entry) (target : RootOutput) (output : FullOutput) : ProbComp Bool :=
  match context.1 with
  | .inl result => pure result
  | .inr pending => RawCtxCheckedParentSecrecy.native source writer continuation (pending, context.2) target output

noncomputable def observed (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : RawCtxCheckedParentSecrecy.Continuation Context M P I D K A S B)
    (context : (Bool ⊕ Context) × Entry) (output : FullOutput) : ProbComp (Trace M P I D K A S B) :=
  match context.1 with
  | .inl result => pure (.inl result)
  | .inr pending => Sum.inr <$> RawCtxSelectedParentHop.observed source writer
      (RawCtxCheckedParentSecrecy.parent continuation) (pending, context.2) output

noncomputable def observer (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : RawCtxCheckedParentSecrecy.Continuation Context M P I D K A S B)
    (context : (Bool ⊕ Context) × Entry) (output : FullOutput) : ProbComp Bool :=
  match context.1 with
  | .inl result => pure result
  | .inr pending => RawCtxSelectedParentHop.observer source writer
      (RawCtxCheckedParentSecrecy.parent continuation) (pending, context.2) output

def candidates : Trace M P I D K A S B → List RootOutput
  | .inl _ => []
  | .inr result => RawCtxSelectedParentHop.candidates result

noncomputable def bad (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : RawCtxCheckedParentSecrecy.Continuation Context M P I D K A S B)
    (context : (Bool ⊕ Context) × Entry) (target : RootOutput) (output : FullOutput) : ProbComp Bool :=
  (fun result => decide (target ∈ candidates result)) <$> observed source writer continuation context output

noncomputable def aliasTester (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : RawCtxCheckedParentSecrecy.Continuation Context M P I D K A S B) :
    FullObserver ((Bool ⊕ Context) × Entry) :=
  RawCtxFullPreimageTester.tester (RawCtxFullPreimageTester.production source)
    (observed source writer continuation) candidates

/-- Common source decisions are identical; the actual pending branch retains its checked three-copy candidate bound. -/
theorem local_bound (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : RawCtxCheckedParentSecrecy.Continuation Context M P I D K A S B)
    (context : (Bool ⊕ Context) × Entry) (target : RootOutput) (output : FullOutput) :
    (native source writer continuation context target output).boolDistAdvantage
      (observer source writer continuation context output) ≤
      3 * Pr{let x ← bad source writer continuation context target output}[x = true].toReal := by
  rcases context with ⟨common | pending, entry⟩
  · refine le_of_eq_of_le ?_ (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)
    simp [native, observer, ProbComp.boolDistAdvantage, -evalDist_apply_singleton, -evalDist_apply_setOf,
      -evalDist_apply_univ]
  · have bad_eq : bad source writer continuation (.inr pending, entry) target output =
        RawCtxSelectedParentHop.bad source writer (RawCtxCheckedParentSecrecy.parent continuation)
          (pending, entry) target output := by
      simp only [bad, observed, Functor.map_map, RawCtxSelectedParentHop.bad]
      congr 1
    rw [native, observer, bad_eq]
    exact RawCtxCheckedParentSecrecy.local_bound source writer continuation (pending, entry) target output

noncomputable def actual (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : RawCtxCheckedParentSecrecy.Continuation Context M P I D K A S B) (sample : ProbComp (Bool ⊕ Context))
    (address : (Bool ⊕ Context) → JointKdfAddress) : ProbComp Bool := do
  let pair ← RawCtxSelectedParentCandidates.sample sample address
  native source writer continuation pair.1 pair.2
    (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList))

noncomputable def random (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : RawCtxCheckedParentSecrecy.Continuation Context M P I D K A S B) (sample : ProbComp (Bool ⊕ Context))
    (address : (Bool ⊕ Context) → JointKdfAddress) : ProbComp Bool := do
  let pair ← RawCtxSelectedParentCandidates.sample sample address
  let output ← $ᵗ FullOutput
  native source writer continuation pair.1 pair.2 output

/-- Averaging the real-child freshness comparison retains the exact full predecessor sampler and charges three copies of its actual input-candidate event. -/
theorem actual_route (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : RawCtxCheckedParentSecrecy.Continuation Context M P I D K A S B) (sample : ProbComp (Bool ⊕ Context))
    (address : (Bool ⊕ Context) → JointKdfAddress) :
    (actual source writer continuation sample address).boolDistAdvantage
      (RawCtxSelectedParentSecrecy.actual source sample address
        (observer source writer continuation)) ≤
      3 * Pr{let pair ← (RawCtxFullPreimageTester.actual (RawCtxFullPreimageTester.production source)
          (RawCtxSelectedParentCandidates.sample sample address)
          (observed source writer continuation))}[pair.1 ∈ candidates pair.2].toReal := by
  have bound := RawCtxScaledBadEventMixture.bind_bound (RawCtxSelectedParentCandidates.sample sample address)
        (fun pair => native source writer continuation pair.1 pair.2
          (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList)))
        (fun pair => observer source writer continuation pair.1
          (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList)))
        (fun pair => bad source writer continuation pair.1 pair.2
          (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList))) 3
        (fun pair => local_bound source writer continuation pair.1 pair.2 _)
  have bindCongr : ∀ {α β γ : Type} (first : ProbComp α) (f : α → ProbComp β) (g : α → ProbComp γ)
      (p : β → Prop) (q : γ → Prop), (∀ a, Pr{let x ← f a}[p x] = Pr{let y ← g a}[q y]) →
        Pr{let x ← first >>= f}[p x] = Pr{let y ← first >>= g}[q y] :=
    fun first f g p q same => prEvent_bind_congr first f g p q same
  have event : Pr{let x ← ((RawCtxSelectedParentCandidates.sample sample address) >>= fun pair =>
        bad source writer continuation pair.1 pair.2
          (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList)))}[x = true] =
      Pr{let pair ← (RawCtxFullPreimageTester.actual (RawCtxFullPreimageTester.production source)
          (RawCtxSelectedParentCandidates.sample sample address)
          (observed source writer continuation))}[pair.1 ∈ candidates pair.2] := by
    rw [RawCtxFullPreimageTester.actual]
    refine bindCongr _ _ _ _ _ fun pair => ?_
    obtain ⟨context, target⟩ := pair
    dsimp only
    rw [bad, prEvent_map, prEvent_map]
    exact prEvent_congr _ _ _ fun result => by simp only [decide_eq_true_eq]
  rw [← event]
  refine le_of_eq_of_le ?_ (bound.trans_eq ?_)
  · simp only [actual, RawCtxSelectedParentSecrecy.actual, RawCtxSelectedParentCandidates.sample, bind_assoc,
      pure_bind]
  · rw [Nat.cast_ofNat]


set_option maxRecDepth 2048 in
/-- The independent-child freshness comparison retains the full delayed-coordinate candidate experiment with the same explicit factor three. -/
theorem random_route (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : RawCtxCheckedParentSecrecy.Continuation Context M P I D K A S B) (sample : ProbComp (Bool ⊕ Context))
    (address : (Bool ⊕ Context) → JointKdfAddress) :
    (random source writer continuation sample address).boolDistAdvantage
      (RawCtxSelectedParentSecrecy.random sample address
        (observer source writer continuation)) ≤
      3 * Pr{let pair ← (RawCtxSelectedParentCandidates.uniform sample address
          (observed source writer continuation))}[pair.1 ∈ candidates pair.2].toReal := by
  have bound := RawCtxScaledBadEventMixture.bind_bound
    (do let pair ← RawCtxSelectedParentCandidates.sample sample address
        let output ← $ᵗ FullOutput
        pure (pair, output))
    (fun value => native source writer continuation value.1.1 value.1.2 value.2)
    (fun value => observer source writer continuation value.1.1 value.2)
    (fun value => bad source writer continuation value.1.1 value.1.2 value.2) 3
    (fun value => local_bound source writer continuation value.1.1 value.1.2 value.2)
  have bindCongr : ∀ {α β γ : Type} (first : ProbComp α) (f : α → ProbComp β) (g : α → ProbComp γ)
      (p : β → Prop) (q : γ → Prop), (∀ a, Pr{let x ← f a}[p x] = Pr{let y ← g a}[q y]) →
        Pr{let x ← first >>= f}[p x] = Pr{let y ← first >>= g}[q y] :=
    fun first f g p q same => prEvent_bind_congr first f g p q same
  have leftEq : (RawCtxSelectedParentCandidates.sample sample address >>= fun pair =>
          ($ᵗ FullOutput) >>= fun output => pure (pair, output)) >>= (fun value => native source writer continuation value.1.1 value.1.2 value.2) =
      random source writer continuation sample address := by
    simp only [random, bind_assoc, pure_bind]
  have rightEq : (RawCtxSelectedParentCandidates.sample sample address >>= fun pair =>
          ($ᵗ FullOutput) >>= fun output => pure (pair, output)) >>= (fun value => observer source writer continuation value.1.1 value.2) =
      RawCtxSelectedParentSecrecy.random sample address (observer source writer continuation) := by
    simp only [RawCtxSelectedParentSecrecy.random, independentFullGame, RawCtxSelectedParentSecrecy.joint,
      RawCtxSelectedParentCandidates.sample, bind_assoc, pure_bind]
  have lhsComp : (RawCtxSelectedParentCandidates.sample sample address >>= fun pair =>
          ($ᵗ FullOutput) >>= fun output => pure (pair, output)) >>= (fun value => bad source writer continuation value.1.1 value.1.2 value.2) =
      RawCtxSelectedParentCandidates.sample sample address >>= fun pair =>
        ($ᵗ FullOutput) >>= fun output => bad source writer continuation pair.1 pair.2 output := by
    simp only [bind_assoc, pure_bind]
  have rhsComp : RawCtxSelectedParentCandidates.uniform sample address (observed source writer continuation) =
      RawCtxSelectedParentCandidates.sample sample address >>= fun pair =>
        (($ᵗ FullOutput) >>= fun child => (observed source writer continuation) pair.1 child) >>= fun result =>
          pure (pair.2, result) := by
    simp only [RawCtxSelectedParentCandidates.uniform, RawCtxSelectedParentSampler.original,
      RawCtxSelectedParentCandidates.sample, bind_assoc, pure_bind]
  have event : Pr{let x ← ((RawCtxSelectedParentCandidates.sample sample address >>= fun pair =>
          ($ᵗ FullOutput) >>= fun output => pure (pair, output)) >>= (fun value => bad source writer continuation value.1.1 value.1.2 value.2))}[x = true] =
      Pr{let pair ← RawCtxSelectedParentCandidates.uniform sample address (observed source writer continuation)}[
        pair.1 ∈ candidates pair.2] := by
    rw [lhsComp, rhsComp]
    refine bindCongr _ _ _ _ _ fun pair => ?_
    rw [bind_pure_comp _ (($ᵗ FullOutput) >>= fun child => (observed source writer continuation) pair.1 child), prEvent_map]
    refine bindCongr _ _ _ _ _ fun output => ?_
    rw [bad, prEvent_map]
    exact prEvent_congr _ _ _ fun result => by simp only [decide_eq_true_eq]
  rw [leftEq, rightEq, event] at bound
  simpa only [Nat.cast_ofNat] using bound


/-- Real-child recovery is charged to the separately constructed full-output tester, with the freshness coefficient applied explicitly to its Extract/HMAC and finite-image terms. -/
theorem actual_bound (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (writer : RawCtxMixedShared.Writer) (continuation : RawCtxCheckedParentSecrecy.Continuation Context M P I D K A S B)
    (sample : ProbComp (Bool ⊕ Context)) (address : (Bool ⊕ Context) → JointKdfAddress) :
    (actual source writer continuation sample address).boolDistAdvantage
      (RawCtxSelectedParentSecrecy.actual source sample address
        (observer source writer continuation)) ≤
      3 * ((2 ^ 352 : ℝ)⁻¹ +
        RawCtxSelectedParentHop.extractLoss hmac sample address (aliasTester source writer continuation) +
        RawCtxSelectedParentHop.hmacLoss hmac sample address (aliasTester source writer continuation)) := by
  have bound := ENNReal.toReal_mono
    (show ((2 ^ 352 : ENNReal)⁻¹ + ENNReal.ofReal (
      RawCtxSelectedParentHop.extractLoss hmac sample address (aliasTester source writer continuation) +
        RawCtxSelectedParentHop.hmacLoss hmac sample address (aliasTester source writer continuation))) ≠ ⊤ by simp)
    (RawCtxSelectedParentCandidates.real_bound source hmac correct sample address
      (observed source writer continuation) candidates)
  have nonnegative : 0 ≤
      RawCtxSelectedParentHop.extractLoss hmac sample address (aliasTester source writer continuation) +
        RawCtxSelectedParentHop.hmacLoss hmac sample address (aliasTester source writer continuation) :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  simpa [ENNReal.toReal_add, ENNReal.toReal_ofReal nonnegative, add_assoc] using
    (actual_route source writer continuation sample address).trans (mul_le_mul_of_nonneg_left bound (by norm_num))


/-- Only the independent-child branch uses the delayed uniform-input guess bound, retaining every prior and repeated candidate and the explicit freshness coefficient. -/
theorem random_bound (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : RawCtxCheckedParentSecrecy.Continuation Context M P I D K A S B) (sample : ProbComp (Bool ⊕ Context))
    (address : (Bool ⊕ Context) → JointKdfAddress) (qCandidates : Nat)
    (bounded : ∀ context output result,
      result ∈ support (observed source writer continuation context output) →
        (candidates result).length ≤ qCandidates) :
    (random source writer continuation sample address).boolDistAdvantage
      (RawCtxSelectedParentSecrecy.random sample address
        (observer source writer continuation)) ≤
      3 * ((qCandidates : ℝ) / (2 ^ 256 : ℝ)) := by
  simpa using (random_route source writer continuation sample address).trans
    (mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono (ENNReal.div_ne_top (by simp) (by simp))
        (RawCtxSelectedParentCandidates.uniform_bound sample address
          (observed source writer continuation)
          candidates qCandidates bounded)) (by norm_num))


private theorem loss_sum {adv first middle last mainExtract mainHmac testExtract testHmac image guess : ℝ}
    (triangle : adv ≤ first + (middle + last))
    (front : first ≤ 3 * (image + testExtract + testHmac))
    (center : middle ≤ mainExtract + mainHmac) (back : last ≤ 3 * guess) :
    adv ≤ mainExtract + mainHmac + 3 * (testExtract + testHmac + image + guess) := by
  linarith

/-- One full parent-to-child secrecy hop with the actual family freshness decision pays its constructed main Extract/HMAC pair and three copies of the tester, image and independent-input terms. -/
theorem bound (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (writer : RawCtxMixedShared.Writer) (continuation : RawCtxCheckedParentSecrecy.Continuation Context M P I D K A S B)
    (sample : ProbComp (Bool ⊕ Context)) (address : (Bool ⊕ Context) → JointKdfAddress) (qCandidates : Nat)
    (bounded : ∀ context output result,
      result ∈ support (observed source writer continuation context output) →
        (candidates result).length ≤ qCandidates) :
    (actual source writer continuation sample address).boolDistAdvantage
      (random source writer continuation sample address) ≤
      RawCtxSelectedParentHop.extractLoss hmac sample address (observer source writer continuation) +
        RawCtxSelectedParentHop.hmacLoss hmac sample address (observer source writer continuation) +
        3 * (RawCtxSelectedParentHop.extractLoss hmac sample address (aliasTester source writer continuation) +
          RawCtxSelectedParentHop.hmacLoss hmac sample address (aliasTester source writer continuation) +
          (2 ^ 352 : ℝ)⁻¹ + (qCandidates : ℝ) / (2 ^ 256 : ℝ)) := by
  have triangle := (ProbComp.boolDistAdvantage_triangle
    (actual source writer continuation sample address)
    (RawCtxSelectedParentSecrecy.actual source sample address
      (observer source writer continuation))
    (random source writer continuation sample address)).trans
      (add_le_add le_rfl (ProbComp.boolDistAdvantage_triangle _
        (RawCtxSelectedParentSecrecy.random sample address
          (observer source writer continuation)) _))
  have main : (RawCtxSelectedParentSecrecy.actual source sample address
      (observer source writer continuation)).boolDistAdvantage
        (RawCtxSelectedParentSecrecy.random sample address
          (observer source writer continuation)) ≤
      RawCtxSelectedParentHop.extractLoss hmac sample address
        (observer source writer continuation) +
          RawCtxSelectedParentHop.hmacLoss hmac sample address
            (observer source writer continuation) :=
    RawCtxSelectedParentSecrecy.primitive_bound source hmac correct sample address
      (observer source writer continuation)
  have back : (RawCtxSelectedParentSecrecy.random sample address
      (observer source writer continuation)).boolDistAdvantage
        (random source writer continuation sample address) ≤ 3 * ((qCandidates : ℝ) / (2 ^ 256 : ℝ)) := by
    simpa only [ProbComp.boolDistAdvantage, abs_sub_comm] using
      random_bound source writer continuation sample address qCandidates bounded
  exact loss_sum triangle (actual_bound source hmac correct writer continuation sample address) main back


/-- Returning a common bit adds no samples, while the pending branch preserves every actual checked-observer sample. -/
theorem observed_bound (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : RawCtxCheckedParentSecrecy.Continuation Context M P I D K A S B) (q : Nat)
    (bounded : ∀ context output, (RawCtxSelectedParentHop.observed source writer
      (RawCtxCheckedParentSecrecy.parent continuation) context output).IsTotalQueryBound q)
    (context : (Bool ⊕ Context) × Entry) (output : FullOutput) :
    (observed source writer continuation context output).IsTotalQueryBound q := by
  rcases context with ⟨common | pending, entry⟩
  · trivial
  · simpa only [observed, IsTotalQueryBound, isQueryBound_map_iff] using bounded (pending, entry) output

noncomputable def reductionObserver (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : RawCtxCheckedParentSecrecy.Continuation Context M P I D K A S B) :
    Bool → FullObserver ((Bool ⊕ Context) × Entry)
  | false => observer source writer continuation
  | true => aliasTester source writer continuation

/-- Both explicitly constructed observers retain the complete stopped-program sampling bill; the additional tester evaluates fixed HKDF locally. -/
theorem observer_bounds (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : RawCtxCheckedParentSecrecy.Continuation Context M P I D K A S B) (q : Nat)
    (bounded : ∀ context output, (observed source writer continuation context output).IsTotalQueryBound q) :
    (∀ context output, (observer source writer continuation context output).IsTotalQueryBound q) ∧
    (∀ context output, (aliasTester source writer continuation context output).IsTotalQueryBound q) := by
  constructor
  · intro context output
    rcases context with ⟨common | pending, entry⟩
    · trivial
    · simpa only [observed, observer, RawCtxSelectedParentHop.observer, IsTotalQueryBound, isQueryBound_map_iff] using
        bounded (Sum.inr pending, entry) output
  · exact RawCtxFullPreimageTester.tester_uniform _ _ _ bounded

/-- Both reductions pay two HMAC queries and the original prefix/full-parent/observation coins; the additional tester pays up to the complete candidate count in real HKDF evaluations. -/
theorem reduction_queries
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : RawCtxCheckedParentSecrecy.Continuation Context M P I D K A S B) (priorSample : ProbComp (Bool ⊕ Context))
    (address : (Bool ⊕ Context) → JointKdfAddress) (qSample qObserve qCandidates : Nat)
    (sampleBound : priorSample.IsTotalQueryBound qSample)
    (observeBound : ∀ context output, (observed source writer continuation context output).IsTotalQueryBound qObserve)
    (candidateBound : ∀ context output result, result ∈ support (observed source writer continuation context output) →
      (candidates result).length ≤ qCandidates) :
    (∀ forTester, let observe := reductionObserver source writer continuation forTester
      (fullExpandReduction .ratchet (RawCtxSelectedParentSecrecy.joint priorSample address) observe).IsQueryBoundP IsHmacChallengeQuery 2 ∧
        (fullExpandReduction .ratchet (RawCtxSelectedParentSecrecy.joint priorSample address) observe).IsQueryBoundP
          PqxdhFullSecretInputKdf.IsHmacUniformQuery ((qSample + 76) + qObserve)) ∧
      (∀ context output result, result ∈ support (observed source writer continuation context output) →
        (RawCtxFullPreimageTester.evaluate output (candidates result)).IsTotalQueryBound qCandidates) := by
  refine ⟨fun forTester => RawCtxSelectedParentSecrecy.reduction_bounds priorSample address _ qSample qObserve sampleBound ?_,
    RawCtxFullPreimageTester.tester_evaluation_bound _ _ candidateBound⟩
  cases forTester
  · exact (observer_bounds source writer continuation qObserve observeBound).1
  · exact (observer_bounds source writer continuation qObserve observeBound).2


/-- Both ordinary-game challengers retain every prior/parent/observer coin, the Extract replacement key and the two random HMAC blocks; the independent full child has its own76-byte bill. -/
theorem challenger_queries
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (writer : RawCtxMixedShared.Writer)
    (continuation : RawCtxCheckedParentSecrecy.Continuation Context M P I D K A S B) (priorSample : ProbComp (Bool ⊕ Context))
    (address : (Bool ⊕ Context) → JointKdfAddress) (qSample qObserve : Nat)
    (sampleBound : priorSample.IsTotalQueryBound qSample)
    (observeBound : ∀ context output, (observed source writer continuation context output).IsTotalQueryBound qObserve)
    (forTester : Bool) :
    let observe := reductionObserver source writer continuation forTester
    let joint := RawCtxSelectedParentSecrecy.joint priorSample address
    (extractRealGame hmac joint (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound
        ((qSample + 76) + qObserve) ∧
      (extractUniformGame joint (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound
        ((qSample + 76) + (64 + qObserve)) ∧
      (hmacPrfRealGame hmac (fullExpandReduction .ratchet joint observe)).IsTotalQueryBound
        (64 + ((qSample + 76) + qObserve)) ∧
      (hmacPrfRandomGame (fullExpandReduction .ratchet joint observe)).IsTotalQueryBound
        ((qSample + 76) + (64 + (64 + qObserve))) ∧
      (RawCtxSelectedParentSecrecy.random priorSample address observe).IsTotalQueryBound
        ((qSample + 76) + (76 + qObserve)) := by
  apply RawCtxSelectedParentSecrecy.challenger_bounds hmac priorSample address _ qSample qObserve sampleBound
  cases forTester
  · exact (observer_bounds source writer continuation qObserve observeBound).1
  · exact (observer_bounds source writer continuation qObserve observeBound).2


/-- Common branches have an empty ledger and pending branches retain exactly the original complete checked ledger and its source-derived bound. -/
theorem candidates_bound (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : RawCtxCheckedParentSecrecy.Continuation Context M P I D K A S B) (q : Nat)
    (bounded : ∀ context output result, result ∈ support (RawCtxSelectedParentHop.observed source writer
      (RawCtxCheckedParentSecrecy.parent continuation) context output) →
      (RawCtxSelectedParentHop.candidates result).length ≤ q)
    (context : (Bool ⊕ Context) × Entry) (output : FullOutput) (result : Trace M P I D K A S B)
    (supported : result ∈ support (observed source writer continuation context output)) :
    (candidates result).length ≤ q := by
  rcases context with ⟨common | pending, entry⟩
  · simp only [observed, mem_support_pure_iff] at supported
    subst result
    exact Nat.zero_le q
  · simp only [observed, support_map, Set.mem_image] at supported
    obtain ⟨original, present, rfl⟩ := supported
    exact bounded (pending, entry) output original present

end BeaconcryptCore.Computational.RawCtxStoppedParentSecrecy

/-- info: 'BeaconcryptCore.Computational.RawCtxStoppedParentSecrecy.local_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxStoppedParentSecrecy.local_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxStoppedParentSecrecy.actual_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxStoppedParentSecrecy.actual_route

/-- info: 'BeaconcryptCore.Computational.RawCtxStoppedParentSecrecy.random_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxStoppedParentSecrecy.random_route

/-- info: 'BeaconcryptCore.Computational.RawCtxStoppedParentSecrecy.actual_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxStoppedParentSecrecy.actual_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxStoppedParentSecrecy.random_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxStoppedParentSecrecy.random_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxStoppedParentSecrecy.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxStoppedParentSecrecy.bound

/-- info: 'BeaconcryptCore.Computational.RawCtxStoppedParentSecrecy.observed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxStoppedParentSecrecy.observed_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxStoppedParentSecrecy.observer_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxStoppedParentSecrecy.observer_bounds

/-- info: 'BeaconcryptCore.Computational.RawCtxStoppedParentSecrecy.reduction_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxStoppedParentSecrecy.reduction_queries

/-- info: 'BeaconcryptCore.Computational.RawCtxStoppedParentSecrecy.challenger_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxStoppedParentSecrecy.challenger_queries

/-- info: 'BeaconcryptCore.Computational.RawCtxStoppedParentSecrecy.candidates_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxStoppedParentSecrecy.candidates_bound

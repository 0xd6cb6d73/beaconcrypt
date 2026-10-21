import BeaconcryptCore.Computational.RawCtxFamilyFreshnessEvent
import BeaconcryptCore.Computational.RawCtxScaledBadEventMixture

/-!
The retained-parent cryptographic hop uses the actual family completion's native freshness decision. Its target-free observer is constructed from that same completion and original read history, not a supplied final freshness equivalence. Both real and independent child branches retain all private routing and exact public fixed HKDF evaluations. The source predecessor sampler and reached tail still require their operational instantiation; these explicit reductions do not assume that arbitrary reached state is uniform.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxFamilyParentSecrecy
open RawCtxFamilySourceFreshness RawCtxFamilyPendingCompiler RawCtxFamilyFreshnessEvent
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxSelectedParentEntry

structure Tail (M P I D K A Value : Type) (S B : Nat) where
  blocked : List RatchetChain
  disclosed : List RatchetChain
  history : RawCtxProtocolReveals.History S B
  outside : Value → OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool
  work : OracleComp PrimitiveSpec (Value × Roles M P I D K S B)
  state : RawCtxSharedPrimitive.SharedState A
  candidates : List RootOutput

structure Continuation (Context M P I D K A Value : Type) (S B : Nat) where
  sender : M → Std.U64
  route : RawCtxServerRouting.SenderDecoder
  decode : RawCtxReceive.FrameDecoder
  cache : Context → RawCtxSelectedParentTable.Prior
  tail : Context × Entry → Tail M P I D K A Value S B

variable {Context M P I D K A Value : Type} {S B : Nat}

noncomputable def parent (continuation : Continuation Context M P I D K A Value S B) :
    RawCtxSelectedParentHop.Continuation Context A (Bool × State M P I D K S B) where
  prior := continuation.cache
  program := fun context => completion continuation.sender continuation.route continuation.decode
    (continuation.tail context).history (continuation.tail context).outside (continuation.tail context).work
  initial := fun context => RawCtxFamilyCompletionFreshness.initial (continuation.tail context).disclosed
    (continuation.tail context).history (continuation.tail context).state (continuation.tail context).candidates
  event := fun context => remainingEvent (continuation.tail context).blocked (continuation.tail context).disclosed

noncomputable def parameters (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : Continuation Context M P I D K A Value S B) (context : Context × Entry)
    (target : RootOutput) (output : FullOutput) : Parameters :=
  ⟨source, writer, continuation.cache context.1, context.2, output,
    RawCtxSelectedParentPrivateRealization.realView source, target⟩

noncomputable def native (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : Continuation Context M P I D K A Value S B) (context : Context × Entry)
    (target : RootOutput) (output : FullOutput) : ProbComp Bool :=
  actualDecision target (continuation.tail context).blocked (continuation.tail context).disclosed <$>
    (simulateQ (observed (parameters source writer continuation context target output))
      ((parent continuation).program context)).run ((parent continuation).initial context)

/-- The actual family freshness event compares with the explicitly constructed target-free parent observer at cost three times its same original candidate event. -/
theorem local_bound (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : Continuation Context M P I D K A Value S B) (context : Context × Entry)
    (target : RootOutput) (output : FullOutput) :
    (native source writer continuation context target output).boolDistAdvantage
      (RawCtxSelectedParentHop.observer source writer (parent continuation) context output) ≤
      3 * Pr{let x ← RawCtxSelectedParentHop.bad source writer (parent continuation) context target output}[x = true].toReal := by
  have event :
      Pr{let result ← RawCtxSelectedParentHop.observed source writer (parent continuation) context output}[target ∈ RawCtxSelectedParentHop.candidates result] =
        Pr{let x ← RawCtxSelectedParentHop.bad source writer (parent continuation) context target output}[x = true] := by
    rw [RawCtxSelectedParentHop.bad, prEvent_map]
    exact prEvent_congr _ _ _ fun result => by simp only [decide_eq_true_eq]
  rw [← event]
  simpa only [native, RawCtxSelectedParentHop.observer, RawCtxSelectedParentHop.observed,
    RawCtxSelectedParentHop.candidates, parent, parameters, masked] using
      completion_bound (parameters source writer continuation context target output)
        continuation.sender continuation.route continuation.decode (continuation.tail context).blocked
        (continuation.tail context).disclosed (continuation.tail context).history (continuation.tail context).outside
        (continuation.tail context).work (continuation.tail context).state (continuation.tail context).candidates

noncomputable def actual (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : Continuation Context M P I D K A Value S B) (sample : ProbComp Context)
    (address : Context → JointKdfAddress) : ProbComp Bool := do
  let pair ← RawCtxSelectedParentCandidates.sample sample address
  native source writer continuation pair.1 pair.2
    (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList))

noncomputable def random (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : Continuation Context M P I D K A Value S B) (sample : ProbComp Context)
    (address : Context → JointKdfAddress) : ProbComp Bool := do
  let pair ← RawCtxSelectedParentCandidates.sample sample address
  let output ← $ᵗ FullOutput
  native source writer continuation pair.1 pair.2 output

/-- Averaging the real-child freshness comparison retains the exact full predecessor sampler and charges three copies of its actual input-candidate event. -/
theorem actual_route (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : Continuation Context M P I D K A Value S B) (sample : ProbComp Context)
    (address : Context → JointKdfAddress) :
    (actual source writer continuation sample address).boolDistAdvantage
      (RawCtxSelectedParentSecrecy.actual source sample address
        (RawCtxSelectedParentHop.observer source writer (parent continuation))) ≤
      3 * Pr{let pair ← (RawCtxFullPreimageTester.actual (RawCtxFullPreimageTester.production source)
          (RawCtxSelectedParentCandidates.sample sample address)
          (RawCtxSelectedParentHop.observed source writer (parent continuation)))}[pair.1 ∈ RawCtxSelectedParentHop.candidates pair.2].toReal := by
  have bound := RawCtxScaledBadEventMixture.bind_bound (RawCtxSelectedParentCandidates.sample sample address)
        (fun pair => native source writer continuation pair.1 pair.2
          (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList)))
        (fun pair => RawCtxSelectedParentHop.observer source writer (parent continuation) pair.1
          (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList)))
        (fun pair => RawCtxSelectedParentHop.bad source writer (parent continuation) pair.1 pair.2
          (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList))) 3
        (fun pair => local_bound source writer continuation pair.1 pair.2 _)
  have bindCongr : ∀ {α β γ : Type} (first : ProbComp α) (f : α → ProbComp β) (g : α → ProbComp γ)
      (p : β → Prop) (q : γ → Prop), (∀ a, Pr{let x ← f a}[p x] = Pr{let y ← g a}[q y]) →
        Pr{let x ← first >>= f}[p x] = Pr{let y ← first >>= g}[q y] :=
    fun first f g p q same => prEvent_bind_congr first f g p q same
  have event : Pr{let x ← ((RawCtxSelectedParentCandidates.sample sample address) >>= fun pair =>
        RawCtxSelectedParentHop.bad source writer (parent continuation) pair.1 pair.2
          (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList)))}[x = true] =
      Pr{let pair ← (RawCtxFullPreimageTester.actual (RawCtxFullPreimageTester.production source)
          (RawCtxSelectedParentCandidates.sample sample address)
          (RawCtxSelectedParentHop.observed source writer (parent continuation)))}[pair.1 ∈ RawCtxSelectedParentHop.candidates pair.2] := by
    rw [RawCtxFullPreimageTester.actual]
    refine bindCongr _ _ _ _ _ fun pair => ?_
    obtain ⟨context, target⟩ := pair
    dsimp only
    rw [RawCtxSelectedParentHop.bad, prEvent_map, prEvent_map]
    exact prEvent_congr _ _ _ fun result => by simp only [decide_eq_true_eq]
  rw [← event]
  refine le_of_eq_of_le ?_ (bound.trans_eq ?_)
  · simp only [actual, RawCtxSelectedParentSecrecy.actual, RawCtxSelectedParentCandidates.sample, bind_assoc,
      pure_bind]
  · rw [Nat.cast_ofNat]

set_option maxRecDepth 2048 in
/-- The independent-child freshness comparison retains the full delayed-coordinate candidate experiment with the same explicit factor three. -/
theorem random_route (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : Continuation Context M P I D K A Value S B) (sample : ProbComp Context)
    (address : Context → JointKdfAddress) :
    (random source writer continuation sample address).boolDistAdvantage
      (RawCtxSelectedParentSecrecy.random sample address
        (RawCtxSelectedParentHop.observer source writer (parent continuation))) ≤
      3 * Pr{let pair ← (RawCtxSelectedParentCandidates.uniform sample address
          (RawCtxSelectedParentHop.observed source writer (parent continuation)))}[pair.1 ∈ RawCtxSelectedParentHop.candidates pair.2].toReal := by
  have bound := RawCtxScaledBadEventMixture.bind_bound
    (do let pair ← RawCtxSelectedParentCandidates.sample sample address
        let output ← $ᵗ FullOutput
        pure (pair, output))
    (fun value => native source writer continuation value.1.1 value.1.2 value.2)
    (fun value => RawCtxSelectedParentHop.observer source writer (parent continuation) value.1.1 value.2)
    (fun value => RawCtxSelectedParentHop.bad source writer (parent continuation) value.1.1 value.1.2 value.2) 3
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
          ($ᵗ FullOutput) >>= fun output => pure (pair, output)) >>= (fun value => RawCtxSelectedParentHop.observer source writer (parent continuation) value.1.1 value.2) =
      RawCtxSelectedParentSecrecy.random sample address (RawCtxSelectedParentHop.observer source writer (parent continuation)) := by
    simp only [RawCtxSelectedParentSecrecy.random, independentFullGame, RawCtxSelectedParentSecrecy.joint,
      RawCtxSelectedParentCandidates.sample, bind_assoc, pure_bind]
  have lhsComp : (RawCtxSelectedParentCandidates.sample sample address >>= fun pair =>
          ($ᵗ FullOutput) >>= fun output => pure (pair, output)) >>= (fun value => RawCtxSelectedParentHop.bad source writer (parent continuation) value.1.1 value.1.2 value.2) =
      RawCtxSelectedParentCandidates.sample sample address >>= fun pair =>
        ($ᵗ FullOutput) >>= fun output => RawCtxSelectedParentHop.bad source writer (parent continuation) pair.1 pair.2 output := by
    simp only [bind_assoc, pure_bind]
  have rhsComp : RawCtxSelectedParentCandidates.uniform sample address (RawCtxSelectedParentHop.observed source writer (parent continuation)) =
      RawCtxSelectedParentCandidates.sample sample address >>= fun pair =>
        (($ᵗ FullOutput) >>= fun child => (RawCtxSelectedParentHop.observed source writer (parent continuation)) pair.1 child) >>= fun result =>
          pure (pair.2, result) := by
    simp only [RawCtxSelectedParentCandidates.uniform, RawCtxSelectedParentSampler.original,
      RawCtxSelectedParentCandidates.sample, bind_assoc, pure_bind]
  have event : Pr{let x ← ((RawCtxSelectedParentCandidates.sample sample address >>= fun pair =>
          ($ᵗ FullOutput) >>= fun output => pure (pair, output)) >>= (fun value => RawCtxSelectedParentHop.bad source writer (parent continuation) value.1.1 value.1.2 value.2))}[x = true] =
      Pr{let pair ← RawCtxSelectedParentCandidates.uniform sample address (RawCtxSelectedParentHop.observed source writer (parent continuation))}[
        pair.1 ∈ RawCtxSelectedParentHop.candidates pair.2] := by
    rw [lhsComp, rhsComp]
    refine bindCongr _ _ _ _ _ fun pair => ?_
    rw [bind_pure_comp _ (($ᵗ FullOutput) >>= fun child => (RawCtxSelectedParentHop.observed source writer (parent continuation)) pair.1 child), prEvent_map]
    refine bindCongr _ _ _ _ _ fun output => ?_
    rw [RawCtxSelectedParentHop.bad, prEvent_map]
    exact prEvent_congr _ _ _ fun result => by simp only [decide_eq_true_eq]
  rw [leftEq, rightEq, event] at bound
  simpa only [Nat.cast_ofNat] using bound

/-- Real-child recovery is charged to the separately constructed full-output tester, with the freshness coefficient applied explicitly to its Extract/HMAC and finite-image terms. -/
theorem actual_bound (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (writer : RawCtxMixedShared.Writer) (continuation : Continuation Context M P I D K A Value S B)
    (sample : ProbComp Context) (address : Context → JointKdfAddress) :
    (actual source writer continuation sample address).boolDistAdvantage
      (RawCtxSelectedParentSecrecy.actual source sample address
        (RawCtxSelectedParentHop.observer source writer (parent continuation))) ≤
      3 * ((2 ^ 352 : ℝ)⁻¹ +
        RawCtxSelectedParentHop.extractLoss hmac sample address (RawCtxSelectedParentHop.aliasTester source writer (parent continuation)) +
        RawCtxSelectedParentHop.hmacLoss hmac sample address (RawCtxSelectedParentHop.aliasTester source writer (parent continuation))) := by
  have bound := ENNReal.toReal_mono
    (show ((2 ^ 352 : ENNReal)⁻¹ + ENNReal.ofReal (
      RawCtxSelectedParentHop.extractLoss hmac sample address (RawCtxSelectedParentHop.aliasTester source writer (parent continuation)) +
        RawCtxSelectedParentHop.hmacLoss hmac sample address (RawCtxSelectedParentHop.aliasTester source writer (parent continuation)))) ≠ ⊤ by simp)
    (RawCtxSelectedParentCandidates.real_bound source hmac correct sample address
      (RawCtxSelectedParentHop.observed source writer (parent continuation)) RawCtxSelectedParentHop.candidates)
  have nonnegative : 0 ≤
      RawCtxSelectedParentHop.extractLoss hmac sample address (RawCtxSelectedParentHop.aliasTester source writer (parent continuation)) +
        RawCtxSelectedParentHop.hmacLoss hmac sample address (RawCtxSelectedParentHop.aliasTester source writer (parent continuation)) :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  simpa [ENNReal.toReal_add, ENNReal.toReal_ofReal nonnegative, add_assoc] using
    (actual_route source writer continuation sample address).trans (mul_le_mul_of_nonneg_left bound (by norm_num))

/-- Only the independent-child branch uses the delayed uniform-input guess bound, retaining every prior and repeated candidate and the explicit freshness coefficient. -/
theorem random_bound (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : Continuation Context M P I D K A Value S B) (sample : ProbComp Context)
    (address : Context → JointKdfAddress) (qCandidates : Nat)
    (bounded : ∀ context output result,
      result ∈ support (RawCtxSelectedParentHop.observed source writer (parent continuation) context output) →
        (RawCtxSelectedParentHop.candidates result).length ≤ qCandidates) :
    (random source writer continuation sample address).boolDistAdvantage
      (RawCtxSelectedParentSecrecy.random sample address
        (RawCtxSelectedParentHop.observer source writer (parent continuation))) ≤
      3 * ((qCandidates : ℝ) / (2 ^ 256 : ℝ)) := by
  simpa using (random_route source writer continuation sample address).trans
    (mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono (ENNReal.div_ne_top (by simp) (by simp))
        (RawCtxSelectedParentCandidates.uniform_bound sample address
          (RawCtxSelectedParentHop.observed source writer (parent continuation))
          RawCtxSelectedParentHop.candidates qCandidates bounded)) (by norm_num))

private theorem loss_sum {adv first middle last mainExtract mainHmac testExtract testHmac image guess : ℝ}
    (triangle : adv ≤ first + (middle + last))
    (front : first ≤ 3 * (image + testExtract + testHmac))
    (center : middle ≤ mainExtract + mainHmac) (back : last ≤ 3 * guess) :
    adv ≤ mainExtract + mainHmac + 3 * (testExtract + testHmac + image + guess) := by
  linarith

/-- One full parent-to-child secrecy hop with the actual family freshness decision pays its constructed main Extract/HMAC pair and three copies of the tester, image and independent-input terms. -/
theorem bound (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (writer : RawCtxMixedShared.Writer) (continuation : Continuation Context M P I D K A Value S B)
    (sample : ProbComp Context) (address : Context → JointKdfAddress) (qCandidates : Nat)
    (bounded : ∀ context output result,
      result ∈ support (RawCtxSelectedParentHop.observed source writer (parent continuation) context output) →
        (RawCtxSelectedParentHop.candidates result).length ≤ qCandidates) :
    (actual source writer continuation sample address).boolDistAdvantage
      (random source writer continuation sample address) ≤
      RawCtxSelectedParentHop.extractLoss hmac sample address (RawCtxSelectedParentHop.observer source writer (parent continuation)) +
        RawCtxSelectedParentHop.hmacLoss hmac sample address (RawCtxSelectedParentHop.observer source writer (parent continuation)) +
        3 * (RawCtxSelectedParentHop.extractLoss hmac sample address (RawCtxSelectedParentHop.aliasTester source writer (parent continuation)) +
          RawCtxSelectedParentHop.hmacLoss hmac sample address (RawCtxSelectedParentHop.aliasTester source writer (parent continuation)) +
          (2 ^ 352 : ℝ)⁻¹ + (qCandidates : ℝ) / (2 ^ 256 : ℝ)) := by
  have triangle := (ProbComp.boolDistAdvantage_triangle
    (actual source writer continuation sample address)
    (RawCtxSelectedParentSecrecy.actual source sample address
      (RawCtxSelectedParentHop.observer source writer (parent continuation)))
    (random source writer continuation sample address)).trans
      (add_le_add le_rfl (ProbComp.boolDistAdvantage_triangle _
        (RawCtxSelectedParentSecrecy.random sample address
          (RawCtxSelectedParentHop.observer source writer (parent continuation))) _))
  have main : (RawCtxSelectedParentSecrecy.actual source sample address
      (RawCtxSelectedParentHop.observer source writer (parent continuation))).boolDistAdvantage
        (RawCtxSelectedParentSecrecy.random sample address
          (RawCtxSelectedParentHop.observer source writer (parent continuation))) ≤
      RawCtxSelectedParentHop.extractLoss hmac sample address
        (RawCtxSelectedParentHop.observer source writer (parent continuation)) +
          RawCtxSelectedParentHop.hmacLoss hmac sample address
            (RawCtxSelectedParentHop.observer source writer (parent continuation)) :=
    RawCtxSelectedParentSecrecy.primitive_bound source hmac correct sample address
      (RawCtxSelectedParentHop.observer source writer (parent continuation))
  have back : (RawCtxSelectedParentSecrecy.random sample address
      (RawCtxSelectedParentHop.observer source writer (parent continuation))).boolDistAdvantage
        (random source writer continuation sample address) ≤ 3 * ((qCandidates : ℝ) / (2 ^ 256 : ℝ)) := by
    simpa only [ProbComp.boolDistAdvantage, abs_sub_comm] using
      random_bound source writer continuation sample address qCandidates bounded
  exact loss_sum triangle (actual_bound source hmac correct writer continuation sample address) main back

/-- The two constructed freshness observers each use two HMAC challenges and the full sampler/parent/observer bill; the real-input tester separately pays its candidate-count full HKDF evaluations. -/
theorem reduction_queries
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : Continuation Context M P I D K A Value S B) (sample : ProbComp Context)
    (address : Context → JointKdfAddress) (qSample qObserve qCandidates : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observeBound : ∀ context output, (RawCtxSelectedParentHop.observed source writer (parent continuation) context output).IsTotalQueryBound qObserve)
    (candidateBound : ∀ context output result, result ∈ support (RawCtxSelectedParentHop.observed source writer (parent continuation) context output) →
      (RawCtxSelectedParentHop.candidates result).length ≤ qCandidates) :
    (∀ forTester, let observe := RawCtxSelectedParentHop.reductionObserver source writer (parent continuation) forTester
      (fullExpandReduction .ratchet (RawCtxSelectedParentSecrecy.joint sample address) observe).IsQueryBoundP IsHmacChallengeQuery 2 ∧
        (fullExpandReduction .ratchet (RawCtxSelectedParentSecrecy.joint sample address) observe).IsQueryBoundP
          PqxdhFullSecretInputKdf.IsHmacUniformQuery ((qSample + 76) + qObserve)) ∧
      (∀ context output result, result ∈ support (RawCtxSelectedParentHop.observed source writer (parent continuation) context output) →
        (RawCtxFullPreimageTester.evaluate output (RawCtxSelectedParentHop.candidates result)).IsTotalQueryBound qCandidates) :=
  RawCtxSelectedParentHop.reduction_queries source writer (parent continuation) sample address
    qSample qObserve qCandidates sampleBound observeBound candidateBound

/-- Each main or tester challenger pays its own Extract replacement key, HMAC blocks and full child draw in addition to the unchanged full prefix/parent/observer bill. -/
theorem challenger_queries
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (writer : RawCtxMixedShared.Writer)
    (continuation : Continuation Context M P I D K A Value S B) (sample : ProbComp Context)
    (address : Context → JointKdfAddress) (qSample qObserve : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observeBound : ∀ context output, (RawCtxSelectedParentHop.observed source writer (parent continuation) context output).IsTotalQueryBound qObserve)
    (forTester : Bool) :
    let observe := RawCtxSelectedParentHop.reductionObserver source writer (parent continuation) forTester
    let joint := RawCtxSelectedParentSecrecy.joint sample address
    (extractRealGame hmac joint (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound
        ((qSample + 76) + qObserve) ∧
      (extractUniformGame joint (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound
        ((qSample + 76) + (64 + qObserve)) ∧
      (hmacPrfRealGame hmac (fullExpandReduction .ratchet joint observe)).IsTotalQueryBound
        (64 + ((qSample + 76) + qObserve)) ∧
      (hmacPrfRandomGame (fullExpandReduction .ratchet joint observe)).IsTotalQueryBound
        ((qSample + 76) + (64 + (64 + qObserve))) ∧
      (RawCtxSelectedParentSecrecy.random sample address observe).IsTotalQueryBound
        ((qSample + 76) + (76 + qObserve)) :=
  RawCtxSelectedParentHop.challenger_queries source hmac writer (parent continuation) sample address
    qSample qObserve sampleBound observeBound forTester

end BeaconcryptCore.Computational.RawCtxFamilyParentSecrecy

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyParentSecrecy.local_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyParentSecrecy.local_bound
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyParentSecrecy.actual_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyParentSecrecy.actual_route
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyParentSecrecy.random_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyParentSecrecy.random_route
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyParentSecrecy.actual_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyParentSecrecy.actual_bound
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyParentSecrecy.random_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyParentSecrecy.random_bound
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyParentSecrecy.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyParentSecrecy.bound
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyParentSecrecy.reduction_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyParentSecrecy.reduction_queries
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyParentSecrecy.challenger_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyParentSecrecy.challenger_queries

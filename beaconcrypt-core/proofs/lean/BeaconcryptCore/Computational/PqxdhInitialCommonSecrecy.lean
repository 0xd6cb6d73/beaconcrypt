import BeaconcryptCore.Computational.PqxdhInitialPublishedEvent
import BeaconcryptCore.Computational.PqxdhInitialPrivateCheckedFreshness
import BeaconcryptCore.Computational.RawCtxStoppedParentSecrecy

/-!
The complete original builder/post observer shares one common/pending sampler. Common outcomes return the original source bit. Pending outcomes run the actual full stopped continuation and lineage checker with the same selected-session publication gate. The native byte freshness decision and its ordinary target-free proxy are compared without conditioning; the complete masked candidate event carries its explicit coefficient three.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialCommonSecrecy
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxSelectedParentEntry
variable {ι Context M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}

structure View (Context : Type) (extra : OracleSpec ι) (M P I D K X Response Shared A N C : Type) (S B : Nat) where
  continuation : PqxdhInitialParentStoppedHop.Continuation Context extra M P I D K X Response Shared A N C Bool Bool S B
  disclosed : List RatchetChain
  earlier : Context → List RatchetChain
  ambient : Context → PqxdhInitialParentObserver.State A N C
  priorCandidates : Context → List RootOutput
  selected : RawCtxProtocolReveals.Owner S B
  number : Std.U64
  remaining : Nat
  depth : ∀ context, continuation.depth context = some remaining

abbrev Trace (M P I D K A N C : Type) (S B : Nat) :=
  Bool ⊕ PqxdhInitialParentStoppedHop.Trace M P I D K A N C Bool Bool S B

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (view : View Context extra M P I D K X Response Shared A N C S B)

noncomputable def native (context : (Bool ⊕ Context) × Entry) (target : RootOutput) (output : FullOutput) : ProbComp Bool :=
  match context.1 with
  | .inl result => pure result
  | .inr pending =>
    PqxdhInitialPrivateCheckedFreshness.actualDecision target (view.earlier pending) view.disclosed
      (fun result => PqxdhInitialPublishedEvent.Gate view.selected view.number result.1.1) <$>
    PqxdhInitialPrivateCheckedFreshness.nativeRun source writer mark sender route decode view.continuation
      (pending, context.2) target output view.disclosed (view.ambient pending) (view.priorCandidates pending)

noncomputable def observed (context : (Bool ⊕ Context) × Entry) (output : FullOutput) : ProbComp (Trace M P I D K A N C S B) :=
  match context.1 with
  | .inl result => pure (.inl result)
  | .inr pending => Sum.inr <$>
    PqxdhInitialCheckedFreshness.maskedRun source writer mark sender route decode view.continuation
      (pending, context.2) output view.disclosed (view.ambient pending) (view.priorCandidates pending)

noncomputable def observer (context : (Bool ⊕ Context) × Entry) (output : FullOutput) : ProbComp Bool :=
  match context.1 with
  | .inl result => pure result
  | .inr pending =>
    PqxdhInitialParentStoppedHop.decision
      (PqxdhInitialPrivateCheckedFreshness.remainingEvent (view.earlier pending) view.disclosed
        (fun result => PqxdhInitialPublishedEvent.Gate view.selected view.number result.1.1)) <$>
    PqxdhInitialCheckedFreshness.maskedRun source writer mark sender route decode view.continuation
      (pending, context.2) output view.disclosed (view.ambient pending) (view.priorCandidates pending)

def candidates : Trace M P I D K A N C S B → List RootOutput
  | .inl _ => []
  | .inr result => PqxdhInitialParentStoppedHop.candidates result

noncomputable def bad (context : (Bool ⊕ Context) × Entry) (target : RootOutput) (output : FullOutput) : ProbComp Bool :=
  (fun result => decide (target ∈ candidates result)) <$> observed source writer mark sender route decode view context output

noncomputable def aliasTester : FullObserver ((Bool ⊕ Context) × Entry) :=
  RawCtxFullPreimageTester.tester (RawCtxFullPreimageTester.production source)
    (observed source writer mark sender route decode view) candidates

/-- The actual publication-gated byte freshness decision differs from the ordinary observer only by three copies of the complete masked candidate event; common decisions are identical. -/
theorem local_bound (context : (Bool ⊕ Context) × Entry) (target : RootOutput) (output : FullOutput) :
    (native source writer mark sender route decode view context target output).boolDistAdvantage
      (observer source writer mark sender route decode view context output) ≤
    3 * Pr[= true | bad source writer mark sender route decode view context target output].toReal := by
  rcases context with ⟨common | pending, entry⟩
  · simp [native, observer, ProbComp.boolDistAdvantage]
  · simpa only [native, observer, bad, observed, Functor.map_map, Function.comp_def, candidates,
      PqxdhInitialPrivateCheckedFreshness.maskedRun, PqxdhInitialCheckedFreshness.maskedRun,
      PqxdhInitialParentStoppedHop.candidates, ← probEvent_eq_eq_probOutput, probEvent_map, decide_eq_true_eq] using
      PqxdhInitialPrivateCheckedFreshness.bound source writer mark sender route decode view.continuation
        (pending, entry) target output view.disclosed (view.ambient pending) (view.priorCandidates pending)
        (view.earlier pending) (fun result => PqxdhInitialPublishedEvent.Gate view.selected view.number result.1.1)
        view.remaining (view.depth pending)

noncomputable def actual (sample : ProbComp (Bool ⊕ Context))
    (address : (Bool ⊕ Context) → JointKdfAddress) : ProbComp Bool := do
  let pair ← RawCtxSelectedParentCandidates.sample sample address
  native source writer mark sender route decode view pair.1 pair.2
    (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList))

noncomputable def random (sample : ProbComp (Bool ⊕ Context))
    (address : (Bool ⊕ Context) → JointKdfAddress) : ProbComp Bool := do
  let pair ← RawCtxSelectedParentCandidates.sample sample address
  let output ← $ᵗ FullOutput
  native source writer mark sender route decode view pair.1 pair.2 output

/-- Averaging the real-child freshness comparison retains the exact full predecessor sampler and charges three copies of its actual input-candidate event. -/
theorem actual_route (sample : ProbComp (Bool ⊕ Context))
    (address : (Bool ⊕ Context) → JointKdfAddress) :
    (actual source writer mark sender route decode view sample address).boolDistAdvantage
      (RawCtxSelectedParentSecrecy.actual source sample address
        (observer source writer mark sender route decode view)) ≤
      3 * Pr[fun pair => pair.1 ∈ candidates pair.2 |
        RawCtxFullPreimageTester.actual (RawCtxFullPreimageTester.production source)
          (RawCtxSelectedParentCandidates.sample sample address)
          (observed source writer mark sender route decode view)].toReal := by
  simpa only [actual, RawCtxSelectedParentSecrecy.actual, RawCtxSelectedParentCandidates.sample,
    RawCtxFullPreimageTester.actual, RawCtxFullPreimageTester.production, bad,
    Nat.cast_ofNat, bind_assoc, pure_bind, ← probEvent_eq_eq_probOutput, probEvent_bind_eq_tsum,
    probEvent_map, Function.comp_def, decide_eq_true_eq, probEvent_pure, mul_ite, mul_one, mul_zero] using
      RawCtxScaledBadEventMixture.bind_bound (RawCtxSelectedParentCandidates.sample sample address)
        (fun pair => native source writer mark sender route decode view pair.1 pair.2
          (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList)))
        (fun pair => observer source writer mark sender route decode view pair.1
          (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList)))
        (fun pair => bad source writer mark sender route decode view pair.1 pair.2
          (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList))) 3
        (fun pair => local_bound source writer mark sender route decode view pair.1 pair.2 _)



set_option maxRecDepth 2048 in
/-- The independent-child freshness comparison retains the full delayed-coordinate candidate experiment with the same explicit factor three. -/
theorem random_route (sample : ProbComp (Bool ⊕ Context))
    (address : (Bool ⊕ Context) → JointKdfAddress) :
    (random source writer mark sender route decode view sample address).boolDistAdvantage
      (RawCtxSelectedParentSecrecy.random sample address
        (observer source writer mark sender route decode view)) ≤
      3 * Pr[fun pair => pair.1 ∈ candidates pair.2 |
        RawCtxSelectedParentCandidates.uniform sample address
          (observed source writer mark sender route decode view)].toReal := by
  have bound := RawCtxScaledBadEventMixture.bind_bound
    (do let pair ← RawCtxSelectedParentCandidates.sample sample address
        let output ← $ᵗ FullOutput
        pure (pair, output))
    (fun value => native source writer mark sender route decode view value.1.1 value.1.2 value.2)
    (fun value => observer source writer mark sender route decode view value.1.1 value.2)
    (fun value => bad source writer mark sender route decode view value.1.1 value.1.2 value.2) 3
    (fun value => local_bound source writer mark sender route decode view value.1.1 value.1.2 value.2)
  simp only [random, RawCtxSelectedParentSecrecy.random, independentFullGame,
    RawCtxSelectedParentSecrecy.joint, RawCtxSelectedParentCandidates.sample,
    RawCtxSelectedParentCandidates.uniform, RawCtxSelectedParentSampler.original, bad,
    Nat.cast_ofNat, bind_assoc, pure_bind] at bound ⊢
  simp only [bind_pure_comp] at bound ⊢
  simpa only [← probEvent_eq_eq_probOutput, probEvent_bind_eq_tsum, probEvent_map,
    Function.comp_def, decide_eq_true_eq] using bound



/-- Real-child recovery is charged to the separately constructed full-output tester, with the freshness coefficient applied explicitly to its Extract/HMAC and finite-image terms. -/
theorem actual_bound (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (writer : RawCtxMixedShared.Writer) (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (view : View Context extra M P I D K X Response Shared A N C S B)
    (sample : ProbComp (Bool ⊕ Context)) (address : (Bool ⊕ Context) → JointKdfAddress) :
    (actual source writer mark sender route decode view sample address).boolDistAdvantage
      (RawCtxSelectedParentSecrecy.actual source sample address
        (observer source writer mark sender route decode view)) ≤
      3 * ((2 ^ 352 : ℝ)⁻¹ +
        RawCtxSelectedParentHop.extractLoss hmac sample address (aliasTester source writer mark sender route decode view) +
        RawCtxSelectedParentHop.hmacLoss hmac sample address (aliasTester source writer mark sender route decode view)) := by
  have bound := ENNReal.toReal_mono
    (show ((2 ^ 352 : ENNReal)⁻¹ + ENNReal.ofReal (
      RawCtxSelectedParentHop.extractLoss hmac sample address (aliasTester source writer mark sender route decode view) +
        RawCtxSelectedParentHop.hmacLoss hmac sample address (aliasTester source writer mark sender route decode view))) ≠ ⊤ by simp)
    (RawCtxSelectedParentCandidates.real_bound source hmac correct sample address
      (observed source writer mark sender route decode view) candidates)
  have nonnegative : 0 ≤
      RawCtxSelectedParentHop.extractLoss hmac sample address (aliasTester source writer mark sender route decode view) +
        RawCtxSelectedParentHop.hmacLoss hmac sample address (aliasTester source writer mark sender route decode view) :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  simpa [ENNReal.toReal_add, ENNReal.toReal_ofReal nonnegative, add_assoc] using
    (actual_route source writer mark sender route decode view sample address).trans (mul_le_mul_of_nonneg_left bound (by norm_num))



/-- Only the independent-child branch uses the delayed uniform-input guess bound, retaining every prior and repeated candidate and the explicit freshness coefficient. -/
theorem random_bound (sample : ProbComp (Bool ⊕ Context))
    (address : (Bool ⊕ Context) → JointKdfAddress) (qCandidates : Nat)
    (bounded : ∀ context output result,
      result ∈ support (observed source writer mark sender route decode view context output) →
        (candidates result).length ≤ qCandidates) :
    (random source writer mark sender route decode view sample address).boolDistAdvantage
      (RawCtxSelectedParentSecrecy.random sample address
        (observer source writer mark sender route decode view)) ≤
      3 * ((qCandidates : ℝ) / (2 ^ 256 : ℝ)) := by
  simpa using (random_route source writer mark sender route decode view sample address).trans
    (mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono (ENNReal.div_ne_top (by simp) (by simp))
        (RawCtxSelectedParentCandidates.uniform_bound sample address
          (observed source writer mark sender route decode view)
          candidates qCandidates bounded)) (by norm_num))



private theorem loss_sum {adv first middle last mainExtract mainHmac testExtract testHmac image guess : ℝ}
    (triangle : adv ≤ first + (middle + last))
    (front : first ≤ 3 * (image + testExtract + testHmac))
    (center : middle ≤ mainExtract + mainHmac) (back : last ≤ 3 * guess) :
    adv ≤ mainExtract + mainHmac + 3 * (testExtract + testHmac + image + guess) := by
  linarith


/-- One full parent-to-child secrecy hop with the actual family freshness decision pays its constructed main Extract/HMAC pair and three copies of the tester, image and independent-input terms. -/
theorem bound (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (writer : RawCtxMixedShared.Writer) (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (view : View Context extra M P I D K X Response Shared A N C S B)
    (sample : ProbComp (Bool ⊕ Context)) (address : (Bool ⊕ Context) → JointKdfAddress) (qCandidates : Nat)
    (bounded : ∀ context output result,
      result ∈ support (observed source writer mark sender route decode view context output) →
        (candidates result).length ≤ qCandidates) :
    (actual source writer mark sender route decode view sample address).boolDistAdvantage
      (random source writer mark sender route decode view sample address) ≤
      RawCtxSelectedParentHop.extractLoss hmac sample address (observer source writer mark sender route decode view) +
        RawCtxSelectedParentHop.hmacLoss hmac sample address (observer source writer mark sender route decode view) +
        3 * (RawCtxSelectedParentHop.extractLoss hmac sample address (aliasTester source writer mark sender route decode view) +
          RawCtxSelectedParentHop.hmacLoss hmac sample address (aliasTester source writer mark sender route decode view) +
          (2 ^ 352 : ℝ)⁻¹ + (qCandidates : ℝ) / (2 ^ 256 : ℝ)) := by
  have triangle := (ProbComp.boolDistAdvantage_triangle
    (actual source writer mark sender route decode view sample address)
    (RawCtxSelectedParentSecrecy.actual source sample address
      (observer source writer mark sender route decode view))
    (random source writer mark sender route decode view sample address)).trans
      (add_le_add le_rfl (ProbComp.boolDistAdvantage_triangle _
        (RawCtxSelectedParentSecrecy.random sample address
          (observer source writer mark sender route decode view)) _))
  have main : (RawCtxSelectedParentSecrecy.actual source sample address
      (observer source writer mark sender route decode view)).boolDistAdvantage
        (RawCtxSelectedParentSecrecy.random sample address
          (observer source writer mark sender route decode view)) ≤
      RawCtxSelectedParentHop.extractLoss hmac sample address
        (observer source writer mark sender route decode view) +
          RawCtxSelectedParentHop.hmacLoss hmac sample address
            (observer source writer mark sender route decode view) :=
    RawCtxSelectedParentSecrecy.primitive_bound source hmac correct sample address
      (observer source writer mark sender route decode view)
  have back : (RawCtxSelectedParentSecrecy.random sample address
      (observer source writer mark sender route decode view)).boolDistAdvantage
        (random source writer mark sender route decode view sample address) ≤ 3 * ((qCandidates : ℝ) / (2 ^ 256 : ℝ)) := by
    simpa only [ProbComp.boolDistAdvantage, abs_sub_comm] using
      random_bound source writer mark sender route decode view sample address qCandidates bounded
  exact loss_sum triangle (actual_bound source hmac correct writer mark sender route decode view sample address) main back



/-- The common branch adds no observer samples; every pending branch retains the entire original stopped source and appended checker's stated bill. -/
theorem observed_bound (q : Nat)
    (bounded : ∀ context output, (PqxdhInitialCheckedFreshness.maskedRun source writer mark sender route decode view.continuation
      context output view.disclosed (view.ambient context.1) (view.priorCandidates context.1)).IsTotalQueryBound q)
    (context : (Bool ⊕ Context) × Entry) (output : FullOutput) :
    (observed source writer mark sender route decode view context output).IsTotalQueryBound q := by
  rcases context with ⟨common | pending, entry⟩
  · trivial
  · simpa only [observed, IsTotalQueryBound, isQueryBound_map_iff] using bounded (pending, entry) output

noncomputable def reductionObserver : Bool → FullObserver ((Bool ⊕ Context) × Entry)
  | false => observer source writer mark sender route decode view
  | true => aliasTester source writer mark sender route decode view

/-- Main and tester observers retain every original source/checker sample. Real fixed-HKDF testing is separately billed local work. -/
theorem observer_bounds (q : Nat)
    (bounded : ∀ context output, (observed source writer mark sender route decode view context output).IsTotalQueryBound q) :
    (∀ context output, (observer source writer mark sender route decode view context output).IsTotalQueryBound q) ∧
    (∀ context output, (aliasTester source writer mark sender route decode view context output).IsTotalQueryBound q) := by
  constructor
  · intro context output
    rcases context with ⟨common | pending, entry⟩
    · trivial
    · simpa only [observed, observer, IsTotalQueryBound, isQueryBound_map_iff] using
        bounded (Sum.inr pending, entry) output
  · exact RawCtxFullPreimageTester.tester_uniform _ _ _ bounded

/-- Both reductions pay two HMAC queries and the original prefix/full-parent/observation coins; the additional tester pays up to the complete candidate count in real HKDF evaluations. -/
theorem reduction_queries
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (view : View Context extra M P I D K X Response Shared A N C S B) (priorSample : ProbComp (Bool ⊕ Context))
    (address : (Bool ⊕ Context) → JointKdfAddress) (qSample qObserve qCandidates : Nat)
    (sampleBound : priorSample.IsTotalQueryBound qSample)
    (observeBound : ∀ context output, (observed source writer mark sender route decode view context output).IsTotalQueryBound qObserve)
    (candidateBound : ∀ context output result, result ∈ support (observed source writer mark sender route decode view context output) →
      (candidates result).length ≤ qCandidates) :
    (∀ forTester, let observe := reductionObserver source writer mark sender route decode view forTester
      (fullExpandReduction .ratchet (RawCtxSelectedParentSecrecy.joint priorSample address) observe).IsQueryBoundP IsHmacChallengeQuery 2 ∧
        (fullExpandReduction .ratchet (RawCtxSelectedParentSecrecy.joint priorSample address) observe).IsQueryBoundP
          PqxdhFullSecretInputKdf.IsHmacUniformQuery ((qSample + 76) + qObserve)) ∧
      (∀ context output result, result ∈ support (observed source writer mark sender route decode view context output) →
        (RawCtxFullPreimageTester.evaluate output (candidates result)).IsTotalQueryBound qCandidates) := by
  refine ⟨fun forTester => RawCtxSelectedParentSecrecy.reduction_bounds priorSample address _ qSample qObserve sampleBound ?_,
    RawCtxFullPreimageTester.tester_evaluation_bound _ _ candidateBound⟩
  cases forTester
  · exact (observer_bounds source writer mark sender route decode view qObserve observeBound).1
  · exact (observer_bounds source writer mark sender route decode view qObserve observeBound).2



/-- Both ordinary-game challengers retain every prior/parent/observer coin, the Extract replacement key and the two random HMAC blocks; the independent full child has its own76-byte bill. -/
theorem challenger_queries
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (writer : RawCtxMixedShared.Writer)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (view : View Context extra M P I D K X Response Shared A N C S B) (priorSample : ProbComp (Bool ⊕ Context))
    (address : (Bool ⊕ Context) → JointKdfAddress) (qSample qObserve : Nat)
    (sampleBound : priorSample.IsTotalQueryBound qSample)
    (observeBound : ∀ context output, (observed source writer mark sender route decode view context output).IsTotalQueryBound qObserve)
    (forTester : Bool) :
    let observe := reductionObserver source writer mark sender route decode view forTester
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
  · exact (observer_bounds source writer mark sender route decode view qObserve observeBound).1
  · exact (observer_bounds source writer mark sender route decode view qObserve observeBound).2



/-- Common outcomes have no candidates; pending outcomes retain the complete original candidate ledger and its actual source-derived bound. -/
theorem candidates_bound (q : Nat)
    (bounded : ∀ context output result, result ∈ support
      (PqxdhInitialCheckedFreshness.maskedRun source writer mark sender route decode view.continuation
        context output view.disclosed (view.ambient context.1) (view.priorCandidates context.1)) →
        (PqxdhInitialParentStoppedHop.candidates result).length ≤ q)
    (context : (Bool ⊕ Context) × Entry) (output : FullOutput) (result : Trace M P I D K A N C S B)
    (supported : result ∈ support (observed source writer mark sender route decode view context output)) :
    (candidates result).length ≤ q := by
  rcases context with ⟨common | pending, entry⟩
  · simp only [observed, mem_support_pure_iff] at supported
    subst result
    exact Nat.zero_le q
  · simp only [observed, support_map, Set.mem_image] at supported
    obtain ⟨original, present, rfl⟩ := supported
    exact bounded (pending, entry) output original present

end BeaconcryptCore.Computational.PqxdhInitialCommonSecrecy

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCommonSecrecy.local_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCommonSecrecy.local_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCommonSecrecy.actual_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCommonSecrecy.actual_route
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCommonSecrecy.random_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCommonSecrecy.random_route
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCommonSecrecy.actual_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCommonSecrecy.actual_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCommonSecrecy.random_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCommonSecrecy.random_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCommonSecrecy.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCommonSecrecy.bound
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCommonSecrecy.observed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCommonSecrecy.observed_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCommonSecrecy.observer_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCommonSecrecy.observer_bounds
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCommonSecrecy.reduction_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCommonSecrecy.reduction_queries
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCommonSecrecy.challenger_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCommonSecrecy.challenger_queries
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCommonSecrecy.candidates_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCommonSecrecy.candidates_bound

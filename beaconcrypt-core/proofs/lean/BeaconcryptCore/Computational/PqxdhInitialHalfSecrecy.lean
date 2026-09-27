import BeaconcryptCore.Computational.PqxdhInitialHalfRetained
import BeaconcryptCore.Computational.RawCtxStoppedParentSecrecy

/-!
The complete firstbuilder/post freshness event is compared at the same full initial-half sampler. The ordinary reduction never receives the hidden chain bytes. Both constructed Extract/HMAC reductions retain the other directional half, all original context and the complete candidate ledger. Literal source and initializer sampling equations are supplied by the source consumer.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialHalfSecrecy
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxSelectedParentEntry PqxdhInitialBeaconAmbient
variable {ι Context M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}

structure View (Context : Type) (extra : OracleSpec ι) (M P I D K X Response Shared A N C : Type) (S B : Nat) where
  execution : Context × Entry → PqxdhInitialHalfProgram.Execution extra M P I D K Bool Bool S B
  prior : Context → RawCtxSelectedParentTable.Prior
  pre : Context → QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C)
  application : Context → Response → Ambient A N C (Option Pqxdh.Bytes)
  initializer : Context × Entry → PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C PqxdhInitialHalfObserverCompiler.InitialReply
  selector : Context → QueryImpl extra (Ambient A N C)
  aux : Context → QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C)
  ambient : Context → PqxdhInitialParentObserver.State A N C
  priorCandidates : Context × Entry → List RootOutput
  disclosed : Context → List RatchetChain
  ancestors : Context → List RatchetChain
  selected : Context → RawCtxProtocolReveals.Owner S B
  number : Context → Std.U64

abbrev Trace (M P I D K A N C : Type) (S B : Nat) :=
  Bool ⊕ PqxdhInitialParentStoppedHop.Trace M P I D K A N C Bool Bool S B

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (mark : Context → PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (view : View Context extra M P I D K X Response Shared A N C S B)

noncomputable def native (context : (Bool ⊕ Context) × Entry) (target : RootOutput) (output : FullOutput) : ProbComp Bool :=
  match context.1 with
  | .inl result => pure result
  | .inr pending =>
    PqxdhInitialHalfCheckedFreshness.actualDecision target (view.ancestors pending) (view.disclosed pending)
        (fun result => PqxdhInitialPublishedEvent.Gate (view.selected pending) (view.number pending) result.1.1) <$>
      PqxdhInitialHalfCheckedFreshness.nativeRun source writer (view.prior pending) context.2
        (view.pre pending) (view.application pending) (view.initializer (pending, context.2)) (view.selector pending) (view.aux pending)
        (mark pending) sender route decode (view.execution (pending, context.2)) ((view.number pending).val - 1) target output
        (view.disclosed pending) (view.ambient pending) (view.priorCandidates (pending, context.2))

noncomputable def observed (context : (Bool ⊕ Context) × Entry) (output : FullOutput) : ProbComp (Trace M P I D K A N C S B) :=
  match context.1 with
  | .inl result => pure (.inl result)
  | .inr pending =>
    Sum.inr <$>
    PqxdhInitialHalfCheckedFreshness.maskedRun source writer (view.prior pending) context.2
        (view.pre pending) (view.application pending) (view.initializer (pending, context.2)) (view.selector pending) (view.aux pending)
        (mark pending) sender route decode (view.execution (pending, context.2)) ((view.number pending).val - 1) output
        (view.disclosed pending) (view.ambient pending) (view.priorCandidates (pending, context.2))

noncomputable def observer (context : (Bool ⊕ Context) × Entry) (output : FullOutput) : ProbComp Bool :=
  match context.1 with
  | .inl result => pure result
  | .inr pending =>
    PqxdhInitialParentStoppedHop.decision
        (PqxdhInitialHalfCheckedFreshness.remainingEvent (view.ancestors pending) (view.disclosed pending)
          (fun result => PqxdhInitialPublishedEvent.Gate (view.selected pending) (view.number pending) result.1.1)) <$>
        PqxdhInitialHalfCheckedFreshness.maskedRun source writer (view.prior pending) context.2
        (view.pre pending) (view.application pending) (view.initializer (pending, context.2)) (view.selector pending) (view.aux pending)
        (mark pending) sender route decode (view.execution (pending, context.2)) ((view.number pending).val - 1) output
        (view.disclosed pending) (view.ambient pending) (view.priorCandidates (pending, context.2))

def candidates : Trace M P I D K A N C S B → List RootOutput
  | .inl _ => []
  | .inr result => result.2.1.2

noncomputable def bad (context : (Bool ⊕ Context) × Entry) (target : RootOutput) (output : FullOutput) : ProbComp Bool :=
  (fun result => decide (target ∈ candidates result)) <$> observed source writer mark sender route decode view context output

noncomputable def aliasTester : FullObserver ((Bool ⊕ Context) × Entry) :=
  RawCtxFullPreimageTester.tester (RawCtxFullPreimageTester.production source)
    (observed source writer mark sender route decode view) candidates

set_option backward.isDefEq.respectTransparency false in
/-- The complete pre-first-send source event and its ordinary full observer pay three copies of the same masked candidate event, with legitimate disclosures excluded by actual freshness. -/
theorem local_bound (context : (Bool ⊕ Context) × Entry) (target : RootOutput) (output : FullOutput) :
    (native source writer mark sender route decode view context target output).boolDistAdvantage
      (observer source writer mark sender route decode view context output) ≤
    3 * Pr[= true | bad source writer mark sender route decode view context target output].toReal := by
  rcases context with ⟨common | pending, entry⟩
  · simp [native, observer, ProbComp.boolDistAdvantage]
  · simpa only [native, observer, bad, observed, Functor.map_map, Function.comp_def, candidates,
      ← probEvent_eq_eq_probOutput, probEvent_map, decide_eq_true_eq] using
      PqxdhInitialHalfCheckedFreshness.bound source writer (view.prior pending) entry
        (view.pre pending) (view.application pending) (view.initializer (pending, entry)) (view.selector pending) (view.aux pending)
        (mark pending) sender route decode (view.execution (pending, entry)) ((view.number pending).val - 1) target output
        (view.disclosed pending) (view.ambient pending) (view.priorCandidates (pending, entry))
        (view.ancestors pending)
        (fun result => PqxdhInitialPublishedEvent.Gate (view.selected pending) (view.number pending) result.1.1)

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
    (writer : RawCtxMixedShared.Writer) (mark : Context → PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
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
    (writer : RawCtxMixedShared.Writer) (mark : Context → PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
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
    (mark : Context → PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
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
    (mark : Context → PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
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




end BeaconcryptCore.Computational.PqxdhInitialHalfSecrecy

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfSecrecy.local_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfSecrecy.local_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfSecrecy.actual_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfSecrecy.actual_route

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfSecrecy.random_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfSecrecy.random_route

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfSecrecy.actual_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfSecrecy.actual_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfSecrecy.random_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfSecrecy.random_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfSecrecy.bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfSecrecy.bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfSecrecy.observer_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfSecrecy.observer_bounds

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfSecrecy.reduction_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfSecrecy.reduction_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialHalfSecrecy.challenger_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialHalfSecrecy.challenger_queries

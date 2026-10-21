import BeaconcryptCore.Computational.RawCtxSelectedParentPrivateEvents
import BeaconcryptCore.Computational.RawCtxSelectedParentCandidates
import BeaconcryptCore.Computational.RawCtxBadEventMixture
import BeaconcryptCore.Computational.RawCtxSelectedParentPrivateRealization

/-!
The retained predecessor hop uses the same actual joint sampler for the main Extract/HMAC observer and the additional real-input recovery tester. Only private KDF callbacks receive the selected full child output. All public HKDF evaluations stay fixed real evaluations. The complete source-derived continuation, shared state, candidate ledger and original unconditioned good event remain together. The actual source cut must instantiate this continuation; no arbitrary reached-state uniformity or global protocol freshness is inferred here.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedParentHop
open RawCtxSelectedChain RawCtxSelectedParentEntry RawCtxSelectedParentTable
open RawCtxSelectedLiveRead RawCtxSelectedLiveTrace RawCtxSelectedLiveCompiler
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf

abbrev Trace (Auxiliary Result : Type) := Result × RawCtxSelectedParentLive.State Auxiliary

structure Continuation (Context Auxiliary Result : Type) where
  prior : Context → Prior
  program : Context × Entry → OracleComp Spec Result
  initial : Context × Entry → RawCtxSelectedParentLive.State Auxiliary
  event : Context × Entry → Trace Auxiliary Result → Prop

noncomputable def observed {Context Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : Continuation Context Auxiliary Result) (context : Context × Entry) (output : FullOutput) :
    ProbComp (Trace Auxiliary Result) :=
  (simulateQ (RawCtxSelectedParentReadMask.observed source writer (continuation.prior context.1) context.2 output
    labelRead (RawCtxSelectedParentPrivateRealization.realView source)) (continuation.program context)).run
      (continuation.initial context)

noncomputable def observer {Context Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : Continuation Context Auxiliary Result) : FullObserver (Context × Entry) :=
  fun context output => RawCtxSelectedParentPrivateEvents.decision (continuation.event context) <$>
    observed source writer continuation context output

noncomputable def privateGame {Context Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : Continuation Context Auxiliary Result) (context : Context × Entry)
    (target : RootOutput) (output : FullOutput) : ProbComp Bool :=
  RawCtxSelectedParentPrivateEvents.decision (continuation.event context) <$>
    (simulateQ (RawCtxSelectedParentPrivate.observed source writer (continuation.prior context.1) context.2 output
      (nativeReader (RawCtxFreshChainCut.concreteChain target))
      (RawCtxSelectedParentPrivateRealization.realView source) target) (continuation.program context)).run
        (continuation.initial context)

def candidates {Auxiliary Result : Type} (result : Trace Auxiliary Result) : List RootOutput := result.2.1.2

noncomputable def bad {Context Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : Continuation Context Auxiliary Result) (context : Context × Entry)
    (target : RootOutput) (output : FullOutput) : ProbComp Bool :=
  (fun result => decide (target ∈ candidates result)) <$> observed source writer continuation context output

/-- The private/native-reader step and its target-free observer pay only the original masked input-candidate event. -/
theorem local_bound {Context Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : Continuation Context Auxiliary Result) (context : Context × Entry)
    (target : RootOutput) (output : FullOutput) :
    (privateGame source writer continuation context target output).boolDistAdvantage
      (observer source writer continuation context output) ≤
      Pr{let x ← bad source writer continuation context target output}[x = true].toReal := by
  have bound := RawCtxSelectedParentPrivateEvents.local_bound source writer
    (continuation.prior context.1) context.2 output target
    (RawCtxSelectedParentPrivateRealization.realView source) (continuation.program context)
    (continuation.initial context) (continuation.event context)
  have event :
      Pr{let result ← observed source writer continuation context output}[target ∈ candidates result] =
        Pr{let x ← bad source writer continuation context target output}[x = true] := by
    rw [bad, prEvent_map]
    exact prEvent_congr _ _ _ fun result => by simp only [decide_eq_true_eq]
  rw [privateGame, observer]
  exact bound.trans_eq (by
    simpa only [observed, candidates] using congrArg ENNReal.toReal event)

noncomputable def actual {Context Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : Continuation Context Auxiliary Result) (priorSample : ProbComp Context)
    (address : Context → JointKdfAddress) : ProbComp Bool := do
  let pair ← RawCtxSelectedParentCandidates.sample priorSample address
  privateGame source writer continuation pair.1 pair.2
    (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList))

noncomputable def random {Context Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : Continuation Context Auxiliary Result) (priorSample : ProbComp Context)
    (address : Context → JointKdfAddress) : ProbComp Bool := do
  let pair ← RawCtxSelectedParentCandidates.sample priorSample address
  let output ← $ᵗ FullOutput
  privateGame source writer continuation pair.1 pair.2 output

/-- The original real-child experiment and its target-free Extract observer differ by the exact real input-candidate event. -/
theorem actual_route {Context Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : Continuation Context Auxiliary Result) (priorSample : ProbComp Context)
    (address : Context → JointKdfAddress) :
    (actual source writer continuation priorSample address).boolDistAdvantage
      (RawCtxSelectedParentSecrecy.actual source priorSample address (observer source writer continuation)) ≤
      Pr{let pair ← (RawCtxFullPreimageTester.actual (RawCtxFullPreimageTester.production source)
          (RawCtxSelectedParentCandidates.sample priorSample address)
          (observed source writer continuation))}[pair.1 ∈ candidates pair.2].toReal := by
  have bound := RawCtxBadEventMixture.bind_bound (RawCtxSelectedParentCandidates.sample priorSample address)
      (fun pair => privateGame source writer continuation pair.1 pair.2
        (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList)))
      (fun pair => observer source writer continuation pair.1
        (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList)))
      (fun pair => bad source writer continuation pair.1 pair.2
        (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList)))
      (fun pair => local_bound source writer continuation pair.1 pair.2 _)
  have bindCongr : ∀ {α β γ : Type} (first : ProbComp α) (f : α → ProbComp β) (g : α → ProbComp γ)
      (p : β → Prop) (q : γ → Prop), (∀ a, Pr{let x ← f a}[p x] = Pr{let y ← g a}[q y]) →
        Pr{let x ← first >>= f}[p x] = Pr{let y ← first >>= g}[q y] :=
    fun first f g p q same => prEvent_bind_congr first f g p q same
  have event : Pr{let x ← (RawCtxSelectedParentCandidates.sample priorSample address >>= fun pair =>
        bad source writer continuation pair.1 pair.2
          (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList)))}[x = true] =
      Pr{let pair ← (RawCtxFullPreimageTester.actual (RawCtxFullPreimageTester.production source)
          (RawCtxSelectedParentCandidates.sample priorSample address)
          (observed source writer continuation))}[pair.1 ∈ candidates pair.2] := by
    rw [RawCtxFullPreimageTester.actual]
    refine bindCongr _ _ _ _ _ fun pair => ?_
    obtain ⟨context, target⟩ := pair
    dsimp only
    rw [bad, prEvent_map, prEvent_map]
    exact prEvent_congr _ _ _ fun result => by simp only [decide_eq_true_eq]
  rw [← event]
  simpa only [actual, RawCtxSelectedParentSecrecy.actual, RawCtxSelectedParentCandidates.sample, bind_assoc,
    pure_bind] using bound

set_option maxRecDepth 2048 in
/-- The independent-child experiment pays the original delayed-coordinate candidate event when returning to the private source interface. -/
theorem random_route {Context Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : Continuation Context Auxiliary Result) (priorSample : ProbComp Context)
    (address : Context → JointKdfAddress) :
    (random source writer continuation priorSample address).boolDistAdvantage
      (RawCtxSelectedParentSecrecy.random priorSample address (observer source writer continuation)) ≤
      Pr{let pair ← RawCtxSelectedParentCandidates.uniform priorSample address (observed source writer continuation)}[pair.1 ∈ candidates pair.2].toReal := by
  have bound := RawCtxBadEventMixture.bind_bound
      (do let pair ← RawCtxSelectedParentCandidates.sample priorSample address
          let output ← $ᵗ FullOutput
          pure (pair, output))
      (fun value => privateGame source writer continuation value.1.1 value.1.2 value.2)
      (fun value => observer source writer continuation value.1.1 value.2)
      (fun value => bad source writer continuation value.1.1 value.1.2 value.2)
      (fun value => local_bound source writer continuation value.1.1 value.1.2 value.2)
  have bindCongr : ∀ {α β γ : Type} (first : ProbComp α) (f : α → ProbComp β) (g : α → ProbComp γ)
      (p : β → Prop) (q : γ → Prop), (∀ a, Pr{let x ← f a}[p x] = Pr{let y ← g a}[q y]) →
        Pr{let x ← first >>= f}[p x] = Pr{let y ← first >>= g}[q y] :=
    fun first f g p q same => prEvent_bind_congr first f g p q same
  have leftEq : (RawCtxSelectedParentCandidates.sample priorSample address >>= fun pair =>
          ($ᵗ FullOutput) >>= fun output => pure (pair, output)) >>= (fun value => privateGame source writer continuation value.1.1 value.1.2 value.2) =
      random source writer continuation priorSample address := by
    simp only [random, bind_assoc, pure_bind]
  have rightEq : (RawCtxSelectedParentCandidates.sample priorSample address >>= fun pair =>
          ($ᵗ FullOutput) >>= fun output => pure (pair, output)) >>= (fun value => observer source writer continuation value.1.1 value.2) =
      RawCtxSelectedParentSecrecy.random priorSample address (observer source writer continuation) := by
    simp only [RawCtxSelectedParentSecrecy.random, independentFullGame, RawCtxSelectedParentSecrecy.joint,
      RawCtxSelectedParentCandidates.sample, bind_assoc, pure_bind]
  have lhsComp : (RawCtxSelectedParentCandidates.sample priorSample address >>= fun pair =>
          ($ᵗ FullOutput) >>= fun output => pure (pair, output)) >>= (fun value => bad source writer continuation value.1.1 value.1.2 value.2) =
      RawCtxSelectedParentCandidates.sample priorSample address >>= fun pair =>
        ($ᵗ FullOutput) >>= fun output => bad source writer continuation pair.1 pair.2 output := by
    simp only [bind_assoc, pure_bind]
  have rhsComp : RawCtxSelectedParentCandidates.uniform priorSample address (observed source writer continuation) =
      RawCtxSelectedParentCandidates.sample priorSample address >>= fun pair =>
        (($ᵗ FullOutput) >>= fun child => observed source writer continuation pair.1 child) >>= fun result =>
          pure (pair.2, result) := by
    simp only [RawCtxSelectedParentCandidates.uniform, RawCtxSelectedParentSampler.original,
      RawCtxSelectedParentCandidates.sample, bind_assoc, pure_bind]
  have event : Pr{let x ← ((RawCtxSelectedParentCandidates.sample priorSample address >>= fun pair =>
          ($ᵗ FullOutput) >>= fun output => pure (pair, output)) >>= (fun value => bad source writer continuation value.1.1 value.1.2 value.2))}[x = true] =
      Pr{let pair ← RawCtxSelectedParentCandidates.uniform priorSample address (observed source writer continuation)}[
        pair.1 ∈ candidates pair.2] := by
    rw [lhsComp, rhsComp]
    refine bindCongr _ _ _ _ _ fun pair => ?_
    rw [bind_pure_comp _ (($ᵗ FullOutput) >>= fun child => observed source writer continuation pair.1 child), prEvent_map]
    refine bindCongr _ _ _ _ _ fun output => ?_
    rw [bad, prEvent_map]
    exact prEvent_congr _ _ _ fun result => by simp only [decide_eq_true_eq]
  rw [leftEq, rightEq, event] at bound
  exact bound

noncomputable def extractLoss {Context : Type} (hmac : HmacSha512)
    (priorSample : ProbComp Context) (address : Context → JointKdfAddress)
    (observe : FullObserver (Context × Entry)) : ℝ :=
  (extractRealGame hmac (RawCtxSelectedParentSecrecy.joint priorSample address)
    (fullExtractReduction hmac .ratchet observe)).boolDistAdvantage
    (extractUniformGame (RawCtxSelectedParentSecrecy.joint priorSample address)
      (fullExtractReduction hmac .ratchet observe))

noncomputable def hmacLoss {Context : Type} (hmac : HmacSha512)
    (priorSample : ProbComp Context) (address : Context → JointKdfAddress)
    (observe : FullObserver (Context × Entry)) : ℝ :=
  (hmacPrfRealGame hmac (fullExpandReduction .ratchet
    (RawCtxSelectedParentSecrecy.joint priorSample address) observe)).boolDistAdvantage
    (hmacPrfRandomGame (fullExpandReduction .ratchet
      (RawCtxSelectedParentSecrecy.joint priorSample address) observe))

noncomputable def aliasTester {Context Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : Continuation Context Auxiliary Result) : FullObserver (Context × Entry) :=
  RawCtxFullPreimageTester.tester (RawCtxFullPreimageTester.production source)
    (observed source writer continuation) candidates

/-- The real private-to-observer comparison pays the separately constructed actual-input tester and its full76 finite-image term. -/
theorem actual_bound {Context Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (writer : RawCtxMixedShared.Writer) (continuation : Continuation Context Auxiliary Result)
    (priorSample : ProbComp Context) (address : Context → JointKdfAddress) :
    (actual source writer continuation priorSample address).boolDistAdvantage
      (RawCtxSelectedParentSecrecy.actual source priorSample address (observer source writer continuation)) ≤
      (2 ^ 352 : ℝ)⁻¹ + extractLoss hmac priorSample address (aliasTester source writer continuation) +
        hmacLoss hmac priorSample address (aliasTester source writer continuation) := by
  have bound := ENNReal.toReal_mono
    (show ((2 ^ 352 : ENNReal)⁻¹ + ENNReal.ofReal (
      extractLoss hmac priorSample address (aliasTester source writer continuation) +
        hmacLoss hmac priorSample address (aliasTester source writer continuation))) ≠ ⊤ by simp)
    (RawCtxSelectedParentCandidates.real_bound source hmac correct priorSample address
      (observed source writer continuation) candidates)
  have nonnegative : 0 ≤ extractLoss hmac priorSample address (aliasTester source writer continuation) +
      hmacLoss hmac priorSample address (aliasTester source writer continuation) :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  simpa [ENNReal.toReal_add, ENNReal.toReal_ofReal nonnegative, add_assoc] using
    (actual_route source writer continuation priorSample address).trans bound

/-- Only the independent-child comparison uses the delayed uniform-coordinate guess bound, with the complete retained candidate list. -/
theorem random_bound {Context Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : Continuation Context Auxiliary Result) (priorSample : ProbComp Context)
    (address : Context → JointKdfAddress) (qCandidates : Nat)
    (bounded : ∀ context output result, result ∈ support (observed source writer continuation context output) →
      (candidates result).length ≤ qCandidates) :
    (random source writer continuation priorSample address).boolDistAdvantage
      (RawCtxSelectedParentSecrecy.random priorSample address (observer source writer continuation)) ≤
      (qCandidates : ℝ) / (2 ^ 256 : ℝ) := by
  simpa using (random_route source writer continuation priorSample address).trans
    (ENNReal.toReal_mono (ENNReal.div_ne_top (by simp) (by simp))
      (RawCtxSelectedParentCandidates.uniform_bound priorSample address
        (observed source writer continuation) candidates qCandidates bounded))

/-- One retained-parent child replacement pays two constructed Extract observers, two ordinary two-query HMAC reductions, the real full-output image term and the separately justified uniform-input guess term. -/
theorem bound {Context Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (writer : RawCtxMixedShared.Writer) (continuation : Continuation Context Auxiliary Result)
    (priorSample : ProbComp Context) (address : Context → JointKdfAddress) (qCandidates : Nat)
    (bounded : ∀ context output result, result ∈ support (observed source writer continuation context output) →
      (candidates result).length ≤ qCandidates) :
    (actual source writer continuation priorSample address).boolDistAdvantage
      (random source writer continuation priorSample address) ≤
      extractLoss hmac priorSample address (observer source writer continuation) +
        hmacLoss hmac priorSample address (observer source writer continuation) +
        extractLoss hmac priorSample address (aliasTester source writer continuation) +
        hmacLoss hmac priorSample address (aliasTester source writer continuation) +
        (2 ^ 352 : ℝ)⁻¹ + (qCandidates : ℝ) / (2 ^ 256 : ℝ) := by
  have triangle := (ProbComp.boolDistAdvantage_triangle
    (actual source writer continuation priorSample address)
    (RawCtxSelectedParentSecrecy.actual source priorSample address (observer source writer continuation))
    (random source writer continuation priorSample address)).trans
      (add_le_add le_rfl (ProbComp.boolDistAdvantage_triangle _
        (RawCtxSelectedParentSecrecy.random priorSample address (observer source writer continuation)) _))
  have main : (RawCtxSelectedParentSecrecy.actual source priorSample address (observer source writer continuation)).boolDistAdvantage
      (RawCtxSelectedParentSecrecy.random priorSample address (observer source writer continuation)) ≤
      extractLoss hmac priorSample address (observer source writer continuation) +
        hmacLoss hmac priorSample address (observer source writer continuation) :=
    RawCtxSelectedParentSecrecy.primitive_bound source hmac correct priorSample address (observer source writer continuation)
  have uniformBound : (RawCtxSelectedParentSecrecy.random priorSample address (observer source writer continuation)).boolDistAdvantage
      (random source writer continuation priorSample address) ≤ (qCandidates : ℝ) / (2 ^ 256 : ℝ) := by
    simpa only [ProbComp.boolDistAdvantage, abs_sub_comm] using
      random_bound source writer continuation priorSample address qCandidates bounded
  simpa only [add_assoc, add_comm, add_left_comm] using
    triangle.trans (add_le_add (actual_bound source hmac correct writer continuation priorSample address)
      (add_le_add main uniformBound))

/-- Both constructed observers retain the complete original observation's uniform budget; the separate candidate tester has its own real-evaluation bill below. -/
theorem observer_bounds {Context Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : Continuation Context Auxiliary Result) (qObserve : Nat)
    (bounded : ∀ context output, (observed source writer continuation context output).IsTotalQueryBound qObserve) :
    (∀ context output, (observer source writer continuation context output).IsTotalQueryBound qObserve) ∧
      (∀ context output, (aliasTester source writer continuation context output).IsTotalQueryBound qObserve) := by
  exact ⟨fun context output => by
      simpa only [observer, IsTotalQueryBound, isQueryBound_map_iff] using bounded context output,
    RawCtxFullPreimageTester.tester_uniform _ _ _ bounded⟩

noncomputable def reductionObserver {Context Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : Continuation Context Auxiliary Result) (forTester : Bool) : FullObserver (Context × Entry) :=
  if forTester then aliasTester source writer continuation else observer source writer continuation

/-- Both reductions pay two HMAC queries and the original prefix/full-parent/observation coins; the additional tester pays up to the complete candidate count in real HKDF evaluations. -/
theorem reduction_queries {Context Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (continuation : Continuation Context Auxiliary Result) (priorSample : ProbComp Context)
    (address : Context → JointKdfAddress) (qSample qObserve qCandidates : Nat)
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
theorem challenger_queries {Context Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512) (writer : RawCtxMixedShared.Writer)
    (continuation : Continuation Context Auxiliary Result) (priorSample : ProbComp Context)
    (address : Context → JointKdfAddress) (qSample qObserve : Nat)
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

end BeaconcryptCore.Computational.RawCtxSelectedParentHop
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentHop.local_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentHop.local_bound
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentHop.actual_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentHop.actual_route
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentHop.random_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentHop.random_route
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentHop.actual_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentHop.actual_bound
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentHop.random_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentHop.random_bound
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentHop.bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentHop.bound
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentHop.observer_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentHop.observer_bounds
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentHop.reduction_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentHop.reduction_queries
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentHop.challenger_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentHop.challenger_queries

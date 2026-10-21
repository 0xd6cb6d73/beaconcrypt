import BeaconcryptCore.Computational.PqxdhInitialParentObserverAliases
import BeaconcryptCore.Computational.PqxdhInitialOriginContext
import BeaconcryptCore.Computational.RawCtxSelectedParentHop
import BeaconcryptCore.Computational.PqxdhInitialStoppedSourceBounds
import BeaconcryptCore.Computational.RawCtxFiniteLineageCheck

/-!
The full stopped comparison uses the actual origin-aware builder/post descriptor. The observer resumes its first-send, record or attempted-finish continuation, then the original complete post client. The retained initializer and all other external computations are explicit context-indexed source handlers. They are fixed before the complete parent76 draw; the ordinary observer never receives its omitted next-chain coordinate. After that exact source continuation, the optional finite private lineage checker retains its actual returned slots, including the selected material key, and bills every additional derivation. The unconditioned decision retains those slots, the original installation/publication trace and the actual direct-read flag. The concrete reached sampler, source freshness predicate and callback bills are separate source consumers, not assumptions of primitive security.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhInitialBeaconAmbient PqxdhInitialParentObserverCompiler PqxdhInitialParentObserver
open RawCtxSelectedParentEntry RawCtxSelectedParentTable
open RawCtxSelectedParentHop (extractLoss hmacLoss)
variable {ι Context M P I D K X Response Shared A N C Result Origin : Type}
  {extra : OracleSpec ι} {S B : Nat}

abbrev SourceFinal (M P I D K Result Origin : Type) (S B : Nat) :=
  Result × (PqxdhInitialPostContext.LabelFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)

abbrev Final (M P I D K Result Origin : Type) (S B : Nat) :=
  SourceFinal M P I D K Result Origin S B × List RawCtxSelectedChain.Slot

abbrev Trace (M P I D K A N C Result Origin : Type) (S B : Nat) :=
  Final M P I D K Result Origin S B × ((State A N C × List RootOutput) × Bool)

structure Continuation (Context : Type) (extra : OracleSpec ι)
    (M P I D K X Response Shared A N C Result Origin : Type) (S B : Nat) where
  cut : Context → PqxdhInitialOriginContext.Context extra M P I D K Result Origin S B
  depth : Context → Option Nat
  prior : Context → Prior
  initial : Context × Entry → (State A N C × List RootOutput) × Bool
  pre : Context → QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C)
  application : Context → Response → Ambient A N C (Option Pqxdh.Bytes)
  initializer : Context → PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C InitialReply
  selector : Context → QueryImpl extra (Ambient A N C)
  aux : Context → QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C)
  event : Context × Entry → Trace M P I D K A N C Result Origin S B → Prop

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (continuation : Continuation Context extra M P I D K X Response Shared A N C Result Origin S B)

def address (context : Context) : JointKdfAddress :=
  PqxdhInitialBuilderContext.address (continuation.cut context).original

noncomputable def checkerCompiler : QueryImpl (RawCtxFiniteLineageCheck.Spec RawCtxSelectedChain.Slot)
    (OracleComp (Spec extra I D K X Response Shared)) :=
  fun input => oldForward (.inl (.inr (.inl (.inl input))))

def checkerBudget : Option Nat → Nat
  | none => 0
  | some depth => depth + 1

noncomputable def checker : Option Nat → OracleComp (Spec extra I D K X Response Shared) (List RawCtxSelectedChain.Slot)
  | none => pure []
  | some depth => simulateQ checkerCompiler
      (RawCtxFiniteLineageCheck.program RawCtxFiniteLineageCheck.labelKey depth .hidden)

noncomputable def baseProgram (context : Context × Entry) :
    OracleComp (Spec extra I D K X Response Shared) (SourceFinal M P I D K Result Origin S B) :=
  simulateQ PqxdhInitialParentObserverCompiler.compiler
    (PqxdhInitialOriginContext.stopped mark sender route decode (continuation.cut context.1) context.2.material)

noncomputable def program (context : Context × Entry) :
    OracleComp (Spec extra I D K X Response Shared) (Final M P I D K Result Origin S B) := do
  let result ← baseProgram mark sender route decode continuation context
  let forbidden ← checker (continuation.depth context.1)
  pure (result, forbidden)

noncomputable def observed (context : Context × Entry) (output : FullOutput) :
    ProbComp (Trace M P I D K A N C Result Origin S B) :=
  (simulateQ (PqxdhInitialParentObserver.observed source writer (continuation.prior context.1) context.2 output
    (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
    (continuation.selector context.1) (continuation.aux context.1) RawCtxSelectedLiveRead.labelRead)
    (program mark sender route decode continuation context)).run (continuation.initial context)

noncomputable def decision (event : Trace M P I D K A N C Result Origin S B → Prop)
    (result : Trace M P I D K A N C Result Origin S B) : Bool := by
  classical
  exact decide (event result ∧ result.2.2 = false)

/-- The complete original event and the final actual direct-read flag are tested together without conditioning. -/
theorem decision_probability (event : Trace M P I D K A N C Result Origin S B → Prop)
    (run : ProbComp (Trace M P I D K A N C Result Origin S B)) :
    Pr{let x ← decision event <$> run}[x = true] = Pr{let result ← run}[event result ∧ result.2.2 = false] := by
  rw [prEvent_map]
  exact prEvent_congr _ _ _ fun result => by simp only [decision, decide_eq_true_eq]

noncomputable def observer : FullObserver (Context × Entry) :=
  fun context output => decision (continuation.event context) <$>
    observed source writer mark sender route decode continuation context output

noncomputable def privateGame (context : Context × Entry) (target : RootOutput) (output : FullOutput) : ProbComp Bool :=
  decision (continuation.event context) <$>
    (simulateQ (PqxdhInitialParentObserverAliases.observed source writer (continuation.prior context.1) context.2 output
      (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
      (continuation.selector context.1) (continuation.aux context.1)
      (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target)
      (program mark sender route decode continuation context)).run (continuation.initial context)

def candidates (result : Trace M P I D K A N C Result Origin S B) : List RootOutput := result.2.1.2

noncomputable def bad (context : Context × Entry) (target : RootOutput) (output : FullOutput) : ProbComp Bool := by
  classical
  exact (fun result => decide (target ∈ candidates result)) <$>
    observed source writer mark sender route decode continuation context output

set_option backward.isDefEq.respectTransparency false in
/-- The original routed, native-reader continuation and the ordinary stopped observer pay the same complete masked candidate event; the clear-bit event retains the actual origin trace. -/
theorem local_bound (context : Context × Entry) (target : RootOutput) (output : FullOutput) :
    (privateGame source writer mark sender route decode continuation context target output).boolDistAdvantage
      (observer source writer mark sender route decode continuation context output) ≤
      Pr{let x ← bad source writer mark sender route decode continuation context target output}[x = true].toReal := by
  have agreement := PqxdhInitialParentObserverAliases.event_good source writer (continuation.prior context.1) context.2 output
    (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
    (continuation.selector context.1) (continuation.aux context.1) target
    (program mark sender route decode continuation context) (continuation.initial context) (continuation.event context)
  rw [privateGame, observer, ProbComp.boolDistAdvantage, ← prEvent_eq_evalDist_singleton _ true,
    ← prEvent_eq_evalDist_singleton _ true, decision_probability, decision_probability, agreement]
  have variation := (abs_probOutput_toReal_sub_le_tvDist
    (decision (continuation.event context) <$>
      (simulateQ (PqxdhInitialParentObserverAliases.observed source writer (continuation.prior context.1) context.2 output
        (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
        (continuation.selector context.1) (continuation.aux context.1) RawCtxSelectedLiveRead.labelRead target)
        (program mark sender route decode continuation context)).run (continuation.initial context))
    (decision (continuation.event context) <$> observed source writer mark sender route decode continuation context output)).trans
      (tvDist_map_le (decision (continuation.event context)) _ _)
  rw [VCVioLegacy.probOutput_eq_prEvent, VCVioLegacy.probOutput_eq_prEvent, decision_probability, decision_probability,
    tvDist_comm] at variation
  have event :
      Pr{let result ← observed source writer mark sender route decode continuation context output}[target ∈ candidates result] =
        Pr{let x ← bad source writer mark sender route decode continuation context target output}[x = true] := by
    rw [bad, prEvent_map]
    exact prEvent_congr _ _ _ fun result => by simp only [decide_eq_true_eq]
  exact (variation.trans (PqxdhInitialParentObserverAliases.distance source writer (continuation.prior context.1) context.2 output
      (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
      (continuation.selector context.1) (continuation.aux context.1) RawCtxSelectedLiveRead.labelRead target
      (program mark sender route decode continuation context) (continuation.initial context))).trans_eq (by
    simpa only [observed, candidates] using congrArg ENNReal.toReal event)

noncomputable def actual
    (priorSample : ProbComp Context) : ProbComp Bool := do
  let pair ← RawCtxSelectedParentCandidates.sample priorSample (address continuation)
  privateGame source writer mark sender route decode continuation pair.1 pair.2
    (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList))

noncomputable def random
    (priorSample : ProbComp Context) : ProbComp Bool := do
  let pair ← RawCtxSelectedParentCandidates.sample priorSample (address continuation)
  let output ← $ᵗ FullOutput
  privateGame source writer mark sender route decode continuation pair.1 pair.2 output

/-- The original real-child experiment and its target-free Extract observer differ by the exact real input-candidate event. -/
theorem actual_route
    (priorSample : ProbComp Context) :
    (actual source writer mark sender route decode continuation priorSample).boolDistAdvantage
      (RawCtxSelectedParentSecrecy.actual source priorSample (address continuation) (observer source writer mark sender route decode continuation)) ≤
      Pr{let pair ← (RawCtxFullPreimageTester.actual (RawCtxFullPreimageTester.production source)
          (RawCtxSelectedParentCandidates.sample priorSample (address continuation))
          (observed source writer mark sender route decode continuation))}[pair.1 ∈ candidates pair.2].toReal := by
  have bound := RawCtxBadEventMixture.bind_bound (RawCtxSelectedParentCandidates.sample priorSample (address continuation))
      (fun pair => privateGame source writer mark sender route decode continuation pair.1 pair.2
        (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList)))
      (fun pair => observer source writer mark sender route decode continuation pair.1
        (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList)))
      (fun pair => bad source writer mark sender route decode continuation pair.1 pair.2
        (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList)))
      (fun pair => local_bound source writer mark sender route decode continuation pair.1 pair.2 _)
  have bindCongr : ∀ {α β γ : Type} (first : ProbComp α) (f : α → ProbComp β) (g : α → ProbComp γ)
      (p : β → Prop) (q : γ → Prop), (∀ a, Pr{let x ← f a}[p x] = Pr{let y ← g a}[q y]) →
        Pr{let x ← first >>= f}[p x] = Pr{let y ← first >>= g}[q y] :=
    fun first f g p q same => prEvent_bind_congr first f g p q same
  have event : Pr{let x ← (RawCtxSelectedParentCandidates.sample priorSample (address continuation) >>= fun pair =>
        bad source writer mark sender route decode continuation pair.1 pair.2
          (productionStream source.crypto (FixedHkdfDomain.ratchet.address pair.2.toList)))}[x = true] =
      Pr{let pair ← (RawCtxFullPreimageTester.actual (RawCtxFullPreimageTester.production source)
          (RawCtxSelectedParentCandidates.sample priorSample (address continuation))
          (observed source writer mark sender route decode continuation))}[pair.1 ∈ candidates pair.2] := by
    rw [RawCtxFullPreimageTester.actual]
    refine bindCongr _ _ _ _ _ fun pair => ?_
    obtain ⟨context, target⟩ := pair
    dsimp only
    rw [bad, prEvent_map, prEvent_map]
    exact prEvent_congr _ _ _ fun result => by simp only [decide_eq_true_eq]
  rw [← event]
  refine le_of_eq_of_le ?_ bound
  simp only [actual, RawCtxSelectedParentSecrecy.actual, RawCtxSelectedParentCandidates.sample, bind_assoc,
    pure_bind]


set_option maxRecDepth 2048 in
/-- The independent-child experiment pays the original delayed-coordinate candidate event when returning to the private source interface. -/
theorem random_route
    (priorSample : ProbComp Context) :
    (random source writer mark sender route decode continuation priorSample).boolDistAdvantage
      (RawCtxSelectedParentSecrecy.random priorSample (address continuation) (observer source writer mark sender route decode continuation)) ≤
      Pr{let pair ← RawCtxSelectedParentCandidates.uniform priorSample (address continuation) (observed source writer mark sender route decode continuation)}[pair.1 ∈ candidates pair.2].toReal := by
  have bound := RawCtxBadEventMixture.bind_bound
      (do let pair ← RawCtxSelectedParentCandidates.sample priorSample (address continuation)
          let output ← $ᵗ FullOutput
          pure (pair, output))
      (fun value => privateGame source writer mark sender route decode continuation value.1.1 value.1.2 value.2)
      (fun value => observer source writer mark sender route decode continuation value.1.1 value.2)
      (fun value => bad source writer mark sender route decode continuation value.1.1 value.1.2 value.2)
      (fun value => local_bound source writer mark sender route decode continuation value.1.1 value.1.2 value.2)
  have bindCongr : ∀ {α β γ : Type} (first : ProbComp α) (f : α → ProbComp β) (g : α → ProbComp γ)
      (p : β → Prop) (q : γ → Prop), (∀ a, Pr{let x ← f a}[p x] = Pr{let y ← g a}[q y]) →
        Pr{let x ← first >>= f}[p x] = Pr{let y ← first >>= g}[q y] :=
    fun first f g p q same => prEvent_bind_congr first f g p q same
  have leftEq : (RawCtxSelectedParentCandidates.sample priorSample (address continuation) >>= fun pair =>
          ($ᵗ FullOutput) >>= fun output => pure (pair, output)) >>=
        (fun value => privateGame source writer mark sender route decode continuation value.1.1 value.1.2 value.2) =
      random source writer mark sender route decode continuation priorSample := by
    simp only [random, bind_assoc, pure_bind]
  have rightEq : (RawCtxSelectedParentCandidates.sample priorSample (address continuation) >>= fun pair =>
          ($ᵗ FullOutput) >>= fun output => pure (pair, output)) >>=
        (fun value => observer source writer mark sender route decode continuation value.1.1 value.2) =
      RawCtxSelectedParentSecrecy.random priorSample (address continuation) (observer source writer mark sender route decode continuation) := by
    simp only [RawCtxSelectedParentSecrecy.random, independentFullGame, RawCtxSelectedParentSecrecy.joint,
      RawCtxSelectedParentCandidates.sample, bind_assoc, pure_bind]
  have lhsComp : (RawCtxSelectedParentCandidates.sample priorSample (address continuation) >>= fun pair =>
          ($ᵗ FullOutput) >>= fun output => pure (pair, output)) >>=
        (fun value => bad source writer mark sender route decode continuation value.1.1 value.1.2 value.2) =
      RawCtxSelectedParentCandidates.sample priorSample (address continuation) >>= fun pair =>
        ($ᵗ FullOutput) >>= fun output => bad source writer mark sender route decode continuation pair.1 pair.2 output := by
    simp only [bind_assoc, pure_bind]
  have rhsComp : RawCtxSelectedParentCandidates.uniform priorSample (address continuation) (observed source writer mark sender route decode continuation) =
      RawCtxSelectedParentCandidates.sample priorSample (address continuation) >>= fun pair =>
        (($ᵗ FullOutput) >>= fun child => observed source writer mark sender route decode continuation pair.1 child) >>= fun result =>
          pure (pair.2, result) := by
    simp only [RawCtxSelectedParentCandidates.uniform, RawCtxSelectedParentSampler.original,
      RawCtxSelectedParentCandidates.sample, bind_assoc, pure_bind]
  have event : Pr{let x ← ((RawCtxSelectedParentCandidates.sample priorSample (address continuation) >>= fun pair =>
          ($ᵗ FullOutput) >>= fun output => pure (pair, output)) >>=
            (fun value => bad source writer mark sender route decode continuation value.1.1 value.1.2 value.2))}[x = true] =
      Pr{let pair ← RawCtxSelectedParentCandidates.uniform priorSample (address continuation) (observed source writer mark sender route decode continuation)}[
        pair.1 ∈ candidates pair.2] := by
    rw [lhsComp, rhsComp]
    refine bindCongr _ _ _ _ _ fun pair => ?_
    rw [bind_pure_comp _ (($ᵗ FullOutput) >>= fun child => observed source writer mark sender route decode continuation pair.1 child), prEvent_map]
    refine bindCongr _ _ _ _ _ fun output => ?_
    rw [bad, prEvent_map]
    exact prEvent_congr _ _ _ fun result => by simp only [decide_eq_true_eq]
  rw [leftEq, rightEq, event] at bound
  exact bound


noncomputable def aliasTester
    : FullObserver (Context × Entry) :=
  RawCtxFullPreimageTester.tester (RawCtxFullPreimageTester.production source)
    (observed source writer mark sender route decode continuation) candidates

/-- The real private-to-observer comparison pays the separately constructed actual-input tester and its full76 finite-image term. -/
theorem actual_bound
    (hmac : HmacSha512) (correct : SourceFullCorrect source hmac) (priorSample : ProbComp Context) :
    (actual source writer mark sender route decode continuation priorSample).boolDistAdvantage
      (RawCtxSelectedParentSecrecy.actual source priorSample (address continuation) (observer source writer mark sender route decode continuation)) ≤
      (2 ^ 352 : ℝ)⁻¹ + extractLoss hmac priorSample (address continuation) (aliasTester source writer mark sender route decode continuation) +
        hmacLoss hmac priorSample (address continuation) (aliasTester source writer mark sender route decode continuation) := by
  have bound := ENNReal.toReal_mono
    (show ((2 ^ 352 : ENNReal)⁻¹ + ENNReal.ofReal (
      extractLoss hmac priorSample (address continuation) (aliasTester source writer mark sender route decode continuation) +
        hmacLoss hmac priorSample (address continuation) (aliasTester source writer mark sender route decode continuation))) ≠ ⊤ by simp)
    (RawCtxSelectedParentCandidates.real_bound source hmac correct priorSample (address continuation)
      (observed source writer mark sender route decode continuation) candidates)
  have nonnegative : 0 ≤ extractLoss hmac priorSample (address continuation) (aliasTester source writer mark sender route decode continuation) +
      hmacLoss hmac priorSample (address continuation) (aliasTester source writer mark sender route decode continuation) :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  simpa [ENNReal.toReal_add, ENNReal.toReal_ofReal nonnegative, add_assoc] using
    (actual_route source writer mark sender route decode continuation priorSample).trans bound


/-- Only the independent-child comparison uses the delayed uniform-coordinate guess bound, with the complete retained candidate list. -/
theorem random_bound
    (priorSample : ProbComp Context) (qCandidates : Nat)
    (bounded : ∀ context output result, result ∈ support (observed source writer mark sender route decode continuation context output) →
      (candidates result).length ≤ qCandidates) :
    (random source writer mark sender route decode continuation priorSample).boolDistAdvantage
      (RawCtxSelectedParentSecrecy.random priorSample (address continuation) (observer source writer mark sender route decode continuation)) ≤
      (qCandidates : ℝ) / (2 ^ 256 : ℝ) := by
  simpa using (random_route source writer mark sender route decode continuation priorSample).trans
    (ENNReal.toReal_mono (ENNReal.div_ne_top (by simp) (by simp))
      (RawCtxSelectedParentCandidates.uniform_bound priorSample (address continuation)
        (observed source writer mark sender route decode continuation) candidates qCandidates bounded))


/-- One retained-parent child replacement pays two constructed Extract observers, two ordinary two-query HMAC reductions, the real full-output image term and the separately justified uniform-input guess term. -/
theorem bound
    (hmac : HmacSha512) (correct : SourceFullCorrect source hmac) (priorSample : ProbComp Context) (qCandidates : Nat)
    (bounded : ∀ context output result, result ∈ support (observed source writer mark sender route decode continuation context output) →
      (candidates result).length ≤ qCandidates) :
    (actual source writer mark sender route decode continuation priorSample).boolDistAdvantage
      (random source writer mark sender route decode continuation priorSample) ≤
      extractLoss hmac priorSample (address continuation) (observer source writer mark sender route decode continuation) +
        hmacLoss hmac priorSample (address continuation) (observer source writer mark sender route decode continuation) +
        extractLoss hmac priorSample (address continuation) (aliasTester source writer mark sender route decode continuation) +
        hmacLoss hmac priorSample (address continuation) (aliasTester source writer mark sender route decode continuation) +
        (2 ^ 352 : ℝ)⁻¹ + (qCandidates : ℝ) / (2 ^ 256 : ℝ) := by
  have triangle := (ProbComp.boolDistAdvantage_triangle
    (actual source writer mark sender route decode continuation priorSample)
    (RawCtxSelectedParentSecrecy.actual source priorSample (address continuation) (observer source writer mark sender route decode continuation))
    (random source writer mark sender route decode continuation priorSample)).trans
      (add_le_add le_rfl (ProbComp.boolDistAdvantage_triangle _
        (RawCtxSelectedParentSecrecy.random priorSample (address continuation) (observer source writer mark sender route decode continuation)) _))
  have main : (RawCtxSelectedParentSecrecy.actual source priorSample (address continuation) (observer source writer mark sender route decode continuation)).boolDistAdvantage
      (RawCtxSelectedParentSecrecy.random priorSample (address continuation) (observer source writer mark sender route decode continuation)) ≤
      extractLoss hmac priorSample (address continuation) (observer source writer mark sender route decode continuation) +
        hmacLoss hmac priorSample (address continuation) (observer source writer mark sender route decode continuation) :=
    RawCtxSelectedParentSecrecy.primitive_bound source hmac correct priorSample (address continuation) (observer source writer mark sender route decode continuation)
  have uniformBound : (RawCtxSelectedParentSecrecy.random priorSample (address continuation) (observer source writer mark sender route decode continuation)).boolDistAdvantage
      (random source writer mark sender route decode continuation priorSample) ≤ (qCandidates : ℝ) / (2 ^ 256 : ℝ) := by
    simpa only [ProbComp.boolDistAdvantage, abs_sub_comm] using
      random_bound source writer mark sender route decode continuation priorSample qCandidates bounded
  simpa only [add_assoc, add_comm, add_left_comm] using
    triangle.trans (add_le_add (actual_bound source writer mark sender route decode continuation hmac correct priorSample)
      (add_le_add main uniformBound))


/-- Both constructed observers retain the complete original observation's uniform budget; the separate candidate tester has its own real-evaluation bill below. -/
theorem observer_bounds
    (qObserve : Nat)
    (bounded : ∀ context output, (observed source writer mark sender route decode continuation context output).IsTotalQueryBound qObserve) :
    (∀ context output, (observer source writer mark sender route decode continuation context output).IsTotalQueryBound qObserve) ∧
      (∀ context output, (aliasTester source writer mark sender route decode continuation context output).IsTotalQueryBound qObserve) := by
  exact ⟨fun context output => by
      simpa only [observer, IsTotalQueryBound, isQueryBound_map_iff] using bounded context output,
    RawCtxFullPreimageTester.tester_uniform _ _ _ bounded⟩


noncomputable def reductionObserver
    (forTester : Bool) : FullObserver (Context × Entry) :=
  if forTester then aliasTester source writer mark sender route decode continuation else observer source writer mark sender route decode continuation

/-- Both reductions pay two HMAC queries and the original prefix/full-parent/observation coins; the additional tester pays up to the complete candidate count in real HKDF evaluations. -/
theorem reduction_queries
    (priorSample : ProbComp Context) (qSample qObserve qCandidates : Nat)
    (sampleBound : priorSample.IsTotalQueryBound qSample)
    (observeBound : ∀ context output, (observed source writer mark sender route decode continuation context output).IsTotalQueryBound qObserve)
    (candidateBound : ∀ context output result, result ∈ support (observed source writer mark sender route decode continuation context output) →
      (candidates result).length ≤ qCandidates) :
    (∀ forTester, let observe := reductionObserver source writer mark sender route decode continuation forTester
      (fullExpandReduction .ratchet (RawCtxSelectedParentSecrecy.joint priorSample (address continuation)) observe).IsQueryBoundP IsHmacChallengeQuery 2 ∧
        (fullExpandReduction .ratchet (RawCtxSelectedParentSecrecy.joint priorSample (address continuation)) observe).IsQueryBoundP
          PqxdhFullSecretInputKdf.IsHmacUniformQuery ((qSample + 76) + qObserve)) ∧
      (∀ context output result, result ∈ support (observed source writer mark sender route decode continuation context output) →
        (RawCtxFullPreimageTester.evaluate output (candidates result)).IsTotalQueryBound qCandidates) := by
  refine ⟨fun forTester => RawCtxSelectedParentSecrecy.reduction_bounds priorSample (address continuation) _ qSample qObserve sampleBound ?_,
    RawCtxFullPreimageTester.tester_evaluation_bound _ _ candidateBound⟩
  cases forTester
  · exact (observer_bounds source writer mark sender route decode continuation qObserve observeBound).1
  · exact (observer_bounds source writer mark sender route decode continuation qObserve observeBound).2


/-- Every main and tester challenger retains the full source sampler, complete parent draw, observer work and its own replacement randomness. -/
theorem challenger_queries
    (hmac : HmacSha512) (priorSample : ProbComp Context) (qSample qObserve : Nat)
    (sampleBound : priorSample.IsTotalQueryBound qSample)
    (observeBound : ∀ context output, (observed source writer mark sender route decode continuation context output).IsTotalQueryBound qObserve)
    (forTester : Bool) :
    let observe := reductionObserver source writer mark sender route decode continuation forTester
    let joint := RawCtxSelectedParentSecrecy.joint priorSample (address continuation)
    (extractRealGame hmac joint (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound
        ((qSample + 76) + qObserve) ∧
      (extractUniformGame joint (fullExtractReduction hmac .ratchet observe)).IsTotalQueryBound
        ((qSample + 76) + (64 + qObserve)) ∧
      (hmacPrfRealGame hmac (fullExpandReduction .ratchet joint observe)).IsTotalQueryBound
        (64 + ((qSample + 76) + qObserve)) ∧
      (hmacPrfRandomGame (fullExpandReduction .ratchet joint observe)).IsTotalQueryBound
        ((qSample + 76) + (64 + (64 + qObserve))) ∧
      (RawCtxSelectedParentSecrecy.random priorSample (address continuation) observe).IsTotalQueryBound
        ((qSample + 76) + (76 + qObserve)) := by
  apply RawCtxSelectedParentSecrecy.challenger_bounds hmac priorSample (address continuation) _ qSample qObserve sampleBound
  cases forTester
  · exact (observer_bounds source writer mark sender route decode continuation qObserve observeBound).1
  · exact (observer_bounds source writer mark sender route decode continuation qObserve observeBound).2


/-- The actual origin-aware first-send/record/finish tail is the complete source interpreter, with the same private routing and initializer root-cache effects, before only the candidate instrumentation is added. -/
theorem base_source (context : Context × Entry) (target : RootOutput) (output : FullOutput) :
    simulateQ (PqxdhInitialParentObserverAliases.handler source writer (continuation.prior context.1) context.2 output
      (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
      (continuation.selector context.1) (continuation.aux context.1)
      (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target)
      (baseProgram mark sender route decode continuation context) =
      flatten (simulateQ (PqxdhInitialParentObserverAliases.sourceHandler source writer (continuation.prior context.1) context.2 output
        (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
        (continuation.selector context.1) (continuation.aux context.1)
        (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target)
        (PqxdhInitialOriginContext.stopped mark sender route decode (continuation.cut context.1) context.2.material)) :=
  PqxdhInitialParentObserverAliases.compiled_source source writer (continuation.prior context.1) context.2 output
    (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
    (continuation.selector context.1) (continuation.aux context.1)
    (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target _

/-- The optional final checker has only its exact finite private derivation budget, independently of every returned reply. -/
theorem checker_total (depth : Option Nat) :
    (checker (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared) depth).IsTotalQueryBound
      (checkerBudget depth) := by
  cases depth with
  | none => trivial
  | some depth =>
      exact PqxdhBeaconPhase2Bounds.simulate_total checkerCompiler _ (depth + 1)
        (RawCtxFiniteLineageCheck.queries RawCtxFiniteLineageCheck.labelKey depth .hidden)
        (fun _ => ⟨by change 0 < 1; decide, fun _ => True.intro⟩)

/-- The literal ordinary program consumes the source-derived full pending/outside certificate and separately bills every final checker derivation. -/
theorem program_total (context : Context × Entry) (qPost : Nat)
    (fits : PqxdhInitialBuilderCertificates.Fits qPost (continuation.cut context.1).original) :
    (program mark sender route decode continuation context).IsTotalQueryBound
      (2 * (255 + qPost * 67) + checkerBudget (continuation.depth context.1)) := by
  exact isTotalQueryBound_bind
    (PqxdhInitialStoppedSourceBounds.compiled_total mark sender route decode
      (continuation.cut context.1) qPost fits context.2.material)
    (fun result => by
      simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
        checker_total (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared)
          (continuation.depth context.1))

private theorem checker_step (context : Context × Entry) (target : RootOutput) (output : FullOutput)
    (reader : RawCtxSelectedLiveTrace.Reader) (input : RawCtxSelectedChain.Slot) :
    simulateQ (PqxdhInitialParentObserverAliases.handler source writer (continuation.prior context.1) context.2 output
      (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
      (continuation.selector context.1) (continuation.aux context.1) reader target) (checkerCompiler input) =
      pure (RawCtxFiniteLineageCheck.routedStep (continuation.prior context.1) context.2 target output input) := by
  apply (simulateQ_spec_query _ _).trans
  rw [PqxdhInitialParentObserverAliases.old_source]
  cases input <;> simp only [RawCtxSelectedParentPrivate.known_send, RawCtxSelectedParentPrivate.hidden_send,
    RawCtxFiniteLineageCheck.routedStep]
  all_goals rfl

noncomputable def checkerTrace (prior : Prior) (entry : Entry) (target : RootOutput) (output : FullOutput) :
    Option Nat → List RawCtxSelectedChain.Slot
  | none => []
  | some depth => RawCtxFiniteLineageCheck.trace RawCtxFiniteLineageCheck.labelKey
      (RawCtxFiniteLineageCheck.routedStep prior entry target output) depth .hidden

/-- The appended private checker evaluates the exact same finite routed lineage, including the selected material key, while retaining every ambient field. -/
theorem checker_source (context : Context × Entry) (target : RootOutput) (output : FullOutput)
    (reader : RawCtxSelectedLiveTrace.Reader) (depth : Option Nat) :
    simulateQ (PqxdhInitialParentObserverAliases.handler source writer (continuation.prior context.1) context.2 output
      (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
      (continuation.selector context.1) (continuation.aux context.1) reader target) (checker depth) =
      pure (checkerTrace (continuation.prior context.1) context.2 target output depth) := by
  cases depth with
  | none => rfl
  | some depth =>
      rw [checker, ← QueryImpl.simulateQ_compose]
      have step : PqxdhInitialParentObserverAliases.handler source writer (continuation.prior context.1) context.2 output
          (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
          (continuation.selector context.1) (continuation.aux context.1) reader target ∘ₛ checkerCompiler =
          (fun input => pure (RawCtxFiniteLineageCheck.routedStep (continuation.prior context.1) context.2 target output input)) :=
        funext (checker_step source writer continuation context target output reader)
      rw [step]
      exact RawCtxFiniteLineageCheck.evaluate RawCtxFiniteLineageCheck.labelKey
        (RawCtxFiniteLineageCheck.routedStep (continuation.prior context.1) context.2 target output) depth .hidden

/-- The complete program retains the exact original stopped source result, origin trace and all ambient effects, then appends only the explicitly evaluated private lineage checker. -/
theorem program_source (context : Context × Entry) (target : RootOutput) (output : FullOutput) :
    simulateQ (PqxdhInitialParentObserverAliases.handler source writer (continuation.prior context.1) context.2 output
      (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
      (continuation.selector context.1) (continuation.aux context.1)
      (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target)
      (program mark sender route decode continuation context) =
      (fun result => (result, checkerTrace (continuation.prior context.1) context.2 target output (continuation.depth context.1))) <$>
        flatten (simulateQ (PqxdhInitialParentObserverAliases.sourceHandler source writer (continuation.prior context.1) context.2 output
          (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
          (continuation.selector context.1) (continuation.aux context.1)
          (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target)
          (PqxdhInitialOriginContext.stopped mark sender route decode (continuation.cut context.1) context.2.material)) := by
  simp only [program, simulateQ_bind, simulateQ_map, base_source, checker_source, bind_pure_comp, map_pure]

end BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.decision_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.decision_probability
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.local_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.local_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.actual_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.actual_route
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.random_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.random_route
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.actual_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.actual_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.random_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.random_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.bound
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.observer_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.observer_bounds
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.reduction_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.reduction_queries
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.challenger_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.challenger_queries
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.base_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.base_source
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.checker_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.checker_total
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.program_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.program_total
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.checker_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.checker_source
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentStoppedHop.program_source

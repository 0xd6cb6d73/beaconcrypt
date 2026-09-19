import BeaconcryptCore.Computational.RawCtxFamilyFreshnessEvent

/-!
A final lineage condition may depend on the returned child output and complete observed execution. The same original source freshness invariant applies pointwise to that target-free function of the final result. This extends the fixed-list comparison without changing the execution, adversary interface or compromise event. The output-dependent blocked list must be built by the consuming source lineage construction; no final freshness equivalence is assumed here.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxFamilyAdaptiveFreshness
open RawCtxFamilySourceFreshness RawCtxFamilyFreshnessProxy RawCtxFamilyPendingCompiler
open RawCtxFamilyCompletionFreshness PqxdhSecretInputKdf RawCtxSelectedChain
variable {M P I D K A Value : Type} {S B : Nat}

abbrev Output (M P I D K A : Type) (S B : Nat) :=
  (Bool × State M P I D K S B) × RawCtxSelectedParentLive.State A

private theorem event_distance {Result : Type} (work : ProbComp Result) (actual proxy bad : Result → Prop)
    (included : ∀ result ∈ support work, actual result → proxy result)
    (agreed : ∀ result ∈ support work, proxy result → ¬ bad result → actual result) :
    |(Pr[actual | work]).toReal - (Pr[proxy | work]).toReal| ≤ (Pr[bad | work]).toReal := by
  have smaller : Pr[actual | work] ≤ Pr[proxy | work] := probEvent_mono included
  have covered : Pr[proxy | work] ≤ Pr[fun result => actual result ∨ bad result | work] :=
    probEvent_mono (fun result reached enabled => Classical.byCases Or.inr (fun safe => Or.inl (agreed result reached enabled safe)))
  have larger := covered.trans (probEvent_or_le work actual bad)
  have smallerReal := ENNReal.toReal_mono probEvent_ne_top smaller
  have largerReal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩) larger
  rw [ENNReal.toReal_add probEvent_ne_top probEvent_ne_top] at largerReal
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr smallerReal)]
  linarith

/-- Actual freshness and its executable proxy differ only through an input alias on a clear-disclosure execution. Direct compromise is excluded by freshness and adds no probability term. -/
theorem completion_good_bound (parameters : Parameters) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (blocked : Output M P I D K A S B → List RatchetChain) (prior : List RatchetChain) (history : RawCtxProtocolReveals.History S B)
    (outside : Value → OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool)
    (work : OracleComp PrimitiveSpec (Value × Roles M P I D K S B))
    (state : RawCtxSharedPrimitive.SharedState A) (candidates : List RootOutput) :
    let execution := (simulateQ (observed parameters) (completion sender route decode history outside work)).run
      (initial prior history state candidates)
    |(Pr[fun result => result.1.1 = true ∧ RawCtxLiveLineage.Fresh
        (RawCtxFreshChainCut.concreteChain parameters.target :: blocked result) prior result.1.2.2 | execution]).toReal -
      (Pr[fun result => result.1.1 = true ∧ Proxy (blocked result) prior result.1.2.2 result.2.2 | execution]).toReal| ≤
      (Pr[fun result => parameters.target ∈ result.2.1.2 ∧ result.2.2 = false | execution]).toReal := by
  apply event_distance
  case agreed =>
    intro result supported enabled safe
    exact ⟨enabled.1, (completion_fresh_proxy parameters sender route decode (blocked result) prior history outside work
      state candidates result supported (fun hit => safe ⟨hit, enabled.2.1⟩)).mpr enabled.2⟩
  case included =>
    exact fun result supported enabled => ⟨enabled.1,
      fresh_clear _ (blocked result) prior _ _
        (completion_invariant parameters sender route decode prior history outside work state candidates result supported).1 enabled.2,
      fun value present => enabled.2 value (List.mem_cons_of_mem _ present)⟩
noncomputable def actualDecision (target : RootOutput) (blocked : Output M P I D K A S B → List RatchetChain) (prior : List RatchetChain)
    (result : (Bool × State M P I D K S B) × RawCtxSelectedParentLive.State A) : Bool :=
  @decide (result.1.1 = true ∧ RawCtxLiveLineage.Fresh
    (RawCtxFreshChainCut.concreteChain target :: blocked result) prior result.1.2.2) (Classical.propDecidable _)

def remainingEvent (blocked : Output M P I D K A S B → List RatchetChain) (prior : List RatchetChain)
    (result : (Bool × State M P I D K S B) × RawCtxSelectedParentLive.State A) : Prop :=
  result.1.1 = true ∧ RawCtxLiveLineage.Fresh (blocked result) prior result.1.2.2

/-- The original in-progress family freshness decision and its target-free proxy pay only the same candidate event on clear-disclosure executions. -/
theorem completion_decision_bound (parameters : Parameters) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (blocked : Output M P I D K A S B → List RatchetChain) (prior : List RatchetChain) (history : RawCtxProtocolReveals.History S B)
    (outside : Value → OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool)
    (work : OracleComp PrimitiveSpec (Value × Roles M P I D K S B))
    (state : RawCtxSharedPrimitive.SharedState A) (candidates : List RootOutput) :
    let execution := (simulateQ (observed parameters)
      (completion sender route decode history outside work)).run (initial prior history state candidates)
    (actualDecision parameters.target blocked prior <$> execution).boolDistAdvantage
      (RawCtxSelectedParentPrivateEvents.decision (remainingEvent blocked prior) <$> execution) ≤
      (Pr[fun result => parameters.target ∈ result.2.1.2 ∧ result.2.2 = false | execution]).toReal := by
  simpa only [ProbComp.boolDistAdvantage, RawCtxSelectedParentPrivateEvents.decision_probability,
    ← probEvent_eq_eq_probOutput, probEvent_map, Function.comp_def, actualDecision, decide_eq_true_eq,
    RawCtxSelectedParentPrivateEvents.decision, remainingEvent, Proxy, and_assoc, and_left_comm, and_comm] using
      completion_good_bound parameters sender route decode blocked prior history outside work state candidates

/-- The complete actual freshness decision pays an explicit factor three times the original target-free candidate event, while every public HKDF evaluation remains the same supplied real interface. -/
theorem completion_bound (parameters : Parameters) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (blocked : Output M P I D K A S B → List RatchetChain) (prior : List RatchetChain) (history : RawCtxProtocolReveals.History S B)
    (outside : Value → OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool)
    (work : OracleComp PrimitiveSpec (Value × Roles M P I D K S B))
    (state : RawCtxSharedPrimitive.SharedState A) (candidates : List RootOutput) :
    let program := completion sender route decode history outside work
    let start := initial prior history state candidates
    (actualDecision parameters.target blocked prior <$> (simulateQ (observed parameters) program).run start).boolDistAdvantage
      (RawCtxSelectedParentPrivateEvents.decision (remainingEvent blocked prior) <$>
        (simulateQ (RawCtxFamilyFreshnessEvent.masked parameters) program).run start) ≤
      3 * (Pr[fun result => parameters.target ∈ result.2.1.2 |
        (simulateQ (RawCtxFamilyFreshnessEvent.masked parameters) program).run start]).toReal := by
  have triangle := ProbComp.boolDistAdvantage_triangle
    (actualDecision parameters.target blocked prior <$>
      (simulateQ (observed parameters) (completion sender route decode history outside work)).run
        (initial prior history state candidates))
    (RawCtxSelectedParentPrivateEvents.decision (remainingEvent blocked prior) <$>
      (simulateQ (observed parameters) (completion sender route decode history outside work)).run
        (initial prior history state candidates))
    (RawCtxSelectedParentPrivateEvents.decision (remainingEvent blocked prior) <$>
      (simulateQ (RawCtxFamilyFreshnessEvent.masked parameters) (completion sender route decode history outside work)).run
        (initial prior history state candidates))
  have first := (completion_decision_bound parameters sender route decode blocked prior history outside work state candidates).trans
    (RawCtxFamilyFreshnessEvent.good_alias_bound parameters (completion sender route decode history outside work) (initial prior history state candidates))
  have second := RawCtxSelectedParentPrivateEvents.local_bound parameters.source parameters.writer parameters.prior
    parameters.entry parameters.output parameters.target parameters.view
    (completion sender route decode history outside work) (initial prior history state candidates) (remainingEvent blocked prior)
  dsimp only [observed, RawCtxFamilyFreshnessEvent.masked] at first triangle ⊢
  linarith

/-- The factor-three freshness comparison applies to the actual reached material-only family context, retaining the pending operation, peer publication, original history and outside LIVE client. -/
theorem stopped_bound (parameters : Parameters) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (blocked : Output M P I D K A S B → List RatchetChain) (prior : List RatchetChain) (request : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (history : RawCtxProtocolReveals.History S B)
    (outside : (RawCtxProtocolRoles.SourceSpec S B).Range request → OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool)
    (inner : RawCtxSelectedFamilyContext.FamilyContext M P I D K
      ((RawCtxProtocolRoles.SourceSpec S B).Range request) S B) (value : PqxdhOrderedChainHybrids.Material)
    (state : RawCtxSharedPrimitive.SharedState A) (candidates : List RootOutput) :
    let program := simulateQ live (RawCtxSelectedFamilyContext.stopped sender route decode
      (.family request history outside inner) value)
    let start := initial prior history state candidates
    (actualDecision parameters.target blocked prior <$> (simulateQ (observed parameters) program).run start).boolDistAdvantage
      (RawCtxSelectedParentPrivateEvents.decision (remainingEvent blocked prior) <$>
        (simulateQ (RawCtxFamilyFreshnessEvent.masked parameters) program).run start) ≤
      3 * (Pr[fun result => parameters.target ∈ result.2.1.2 |
        (simulateQ (RawCtxFamilyFreshnessEvent.masked parameters) program).run start]).toReal := by
  dsimp only
  rw [stopped_source]
  exact completion_bound parameters sender route decode blocked prior history outside _ state candidates

end BeaconcryptCore.Computational.RawCtxFamilyAdaptiveFreshness

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyAdaptiveFreshness.completion_good_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyAdaptiveFreshness.completion_good_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyAdaptiveFreshness.completion_decision_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyAdaptiveFreshness.completion_decision_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyAdaptiveFreshness.completion_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyAdaptiveFreshness.completion_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyAdaptiveFreshness.stopped_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyAdaptiveFreshness.stopped_bound

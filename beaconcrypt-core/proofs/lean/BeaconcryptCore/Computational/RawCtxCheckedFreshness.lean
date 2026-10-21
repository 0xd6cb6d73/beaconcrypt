import BeaconcryptCore.Computational.RawCtxFamilyLineageCompletion

/-!
The final checked family execution uses one original byte-value freshness event. Its private lineage is computed only after the adversary stops, under the same derivation interface and candidate log. The comparison excludes actual forbidden disclosures through freshness and charges only the complete masked candidate event, with coefficient three. Earlier ancestors are retained; their original-direction source linkage is consumed by the global ordered hybrid.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxCheckedFreshness
open RawCtxSelectedChain RawCtxFamilySourceFreshness RawCtxFamilyPendingCompiler
open RawCtxFamilyCompletionFreshness RawCtxFamilyFreshnessProxy RawCtxFamilyLineageCompletion
open PqxdhSecretInputKdf
variable {M P I D K A Value : Type} {S B : Nat}

abbrev Output (M P I D K A : Type) (S B : Nat) :=
  ((Bool × State M P I D K S B) × List Slot) × RawCtxSelectedParentLive.State A

noncomputable def actualDecision (target : RootOutput) (earlier prior : List RatchetChain)
    (result : Output M P I D K A S B) : Bool :=
  @decide (result.1.1.1 = true ∧ RawCtxLiveLineage.Fresh
    (result.1.2.map (interpret (RawCtxFreshChainCut.concreteChain target)) ++ earlier) prior result.1.1.2.2)
    (Classical.propDecidable _)

def remainingEvent (earlier prior : List RatchetChain) (result : Output M P I D K A S B) : Prop :=
  result.1.1.1 = true ∧ RawCtxLiveLineage.Fresh (RawCtxFiniteLineageCheck.knownValues result.1.2 ++ earlier) prior result.1.1.2.2

private theorem event_distance {Result : Type} (work : ProbComp Result) (actual proxy bad : Result → Prop)
    (included : ∀ result ∈ support work, actual result → proxy result)
    (agreed : ∀ result ∈ support work, proxy result → ¬ bad result → actual result) :
    |(Pr{let x ← work}[actual x]).toReal - (Pr{let x ← work}[proxy x]).toReal| ≤ (Pr{let x ← work}[bad x]).toReal := by
  have smaller : Pr{let x ← work}[actual x] ≤ Pr{let x ← work}[proxy x] := prEvent_mono_of_support _ _ _ included
  have covered : Pr{let x ← work}[proxy x] ≤ Pr{let result ← work}[actual result ∨ bad result] :=
    prEvent_mono_of_support _ _ _ (fun result reached enabled => Classical.byCases Or.inr (fun safe => Or.inl (agreed result reached enabled safe)))
  have larger := covered.trans (prEvent_or_le work actual bad)
  have smallerReal := ENNReal.toReal_mono (prEvent_ne_top _) smaller
  have largerReal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨(prEvent_ne_top _), (prEvent_ne_top _)⟩) larger
  rw [ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)] at largerReal
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr smallerReal)]
  linarith

/-- The actual interpreted final lineage and its executable proxy differ only at an alias on a clear-disclosure execution; direct compromise adds no probability term. -/
theorem good_bound (parameters : Parameters) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (earlier prior : List RatchetChain) (history : RawCtxProtocolReveals.History S B)
    (outside : Value → OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool)
    (work : OracleComp PrimitiveSpec (Value × Roles M P I D K S B)) (n : Nat)
    (state : RawCtxSharedPrimitive.SharedState A) (candidates : List RootOutput) :
    let execution := (simulateQ (observed parameters) (checked sender route decode history outside work n)).run
      (initial prior history state candidates)
    |(Pr{let result ← execution}[result.1.1.1 = true ∧ RawCtxLiveLineage.Fresh
        (result.1.2.map (interpret (RawCtxFreshChainCut.concreteChain parameters.target)) ++ earlier) prior result.1.1.2.2]).toReal -
      (Pr{let result ← execution}[result.1.1.1 = true ∧ Proxy (RawCtxFiniteLineageCheck.knownValues result.1.2 ++ earlier)
        prior result.1.1.2.2 result.2.2]).toReal| ≤
      (Pr{let result ← execution}[parameters.target ∈ result.2.1.2 ∧ result.2.2 = false]).toReal := by
  apply event_distance
  case agreed =>
    intro result supported enabled safe
    exact ⟨enabled.1, (checked_fresh_proxy parameters sender route decode earlier prior history outside work n
      state candidates result supported (fun hit => safe ⟨hit, enabled.2.1⟩)).mpr enabled.2⟩
  case included =>
    intro result supported enabled
    have actual := (checked_fresh parameters sender route decode earlier prior history outside work n
      state candidates result supported).mp enabled.2
    exact ⟨enabled.1,
      fresh_clear _ _ prior _ _
        (checked_invariant parameters sender route decode prior history outside work n state candidates result supported).1 actual,
      fun value present => actual value (List.mem_cons_of_mem _ present)⟩

/-- The Boolean final experiment uses the same original decision and complete checked lineage, with no conditioning on freshness. -/
theorem decision_bound (parameters : Parameters) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (earlier prior : List RatchetChain) (history : RawCtxProtocolReveals.History S B)
    (outside : Value → OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool)
    (work : OracleComp PrimitiveSpec (Value × Roles M P I D K S B)) (n : Nat)
    (state : RawCtxSharedPrimitive.SharedState A) (candidates : List RootOutput) :
    let execution := (simulateQ (observed parameters) (checked sender route decode history outside work n)).run
      (initial prior history state candidates)
    (actualDecision parameters.target earlier prior <$> execution).boolDistAdvantage
      (RawCtxSelectedParentPrivateEvents.decision (remainingEvent earlier prior) <$> execution) ≤
      (Pr{let result ← execution}[parameters.target ∈ result.2.1.2 ∧ result.2.2 = false]).toReal := by
  dsimp only
  simp only [ProbComp.boolDistAdvantage]
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true,
    RawCtxSelectedParentPrivateEvents.decision_probability, prEvent_map]
  simpa only [actualDecision, decide_eq_true_eq,
    RawCtxSelectedParentPrivateEvents.decision, remainingEvent, Proxy, and_assoc, and_left_comm, and_comm] using
      good_bound parameters sender route decode earlier prior history outside work n state candidates

/-- The complete original checked final event differs from its target-free masked observer by at most three copies of the same full candidate event, including every appended checker input. -/
theorem bound (parameters : Parameters) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (earlier prior : List RatchetChain) (history : RawCtxProtocolReveals.History S B)
    (outside : Value → OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool)
    (work : OracleComp PrimitiveSpec (Value × Roles M P I D K S B)) (n : Nat)
    (state : RawCtxSharedPrimitive.SharedState A) (candidates : List RootOutput) :
    let program := checked sender route decode history outside work n
    let start := initial prior history state candidates
    (actualDecision parameters.target earlier prior <$> (simulateQ (observed parameters) program).run start).boolDistAdvantage
      (RawCtxSelectedParentPrivateEvents.decision (remainingEvent earlier prior) <$>
        (simulateQ (RawCtxFamilyFreshnessEvent.masked parameters) program).run start) ≤
      3 * (Pr{let result ← (simulateQ (RawCtxFamilyFreshnessEvent.masked parameters) program).run start}[parameters.target ∈ result.2.1.2]).toReal := by
  have triangle := ProbComp.boolDistAdvantage_triangle
    (actualDecision parameters.target earlier prior <$>
      (simulateQ (observed parameters) (checked sender route decode history outside work n)).run
        (initial prior history state candidates))
    (RawCtxSelectedParentPrivateEvents.decision (remainingEvent earlier prior) <$>
      (simulateQ (observed parameters) (checked sender route decode history outside work n)).run
        (initial prior history state candidates))
    (RawCtxSelectedParentPrivateEvents.decision (remainingEvent earlier prior) <$>
      (simulateQ (RawCtxFamilyFreshnessEvent.masked parameters) (checked sender route decode history outside work n)).run
        (initial prior history state candidates))
  have first := (decision_bound parameters sender route decode earlier prior history outside work n state candidates).trans
    (RawCtxFamilyFreshnessEvent.good_alias_bound parameters (checked sender route decode history outside work n)
      (initial prior history state candidates))
  have second := RawCtxSelectedParentPrivateEvents.local_bound parameters.source parameters.writer parameters.prior
    parameters.entry parameters.output parameters.target parameters.view
    (checked sender route decode history outside work n) (initial prior history state candidates) (remainingEvent earlier prior)
  dsimp only [observed, RawCtxFamilyFreshnessEvent.masked] at first triangle ⊢
  linarith

end BeaconcryptCore.Computational.RawCtxCheckedFreshness

/-- info: 'BeaconcryptCore.Computational.RawCtxCheckedFreshness.good_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCheckedFreshness.good_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxCheckedFreshness.decision_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCheckedFreshness.decision_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxCheckedFreshness.bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCheckedFreshness.bound

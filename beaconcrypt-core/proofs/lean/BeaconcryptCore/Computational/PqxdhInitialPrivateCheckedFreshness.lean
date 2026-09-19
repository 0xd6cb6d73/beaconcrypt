import BeaconcryptCore.Computational.PqxdhInitialCheckedFreshness
import BeaconcryptCore.Computational.PqxdhInitialParentPrivateObserver

/-!
The actual partial-routing stopped builder/post execution and its finite checker use the original byte-value freshness predicate, including prior disclosures and ancestors. Every original initializer returns its unchanged optional kernel, including input aliases; only old private ratchet callbacks are routed. The target-free proxy retains the same original publication gate and complete source result. Its discrepancy charges only input aliases on a clear-disclosure execution; actual forbidden reads are excluded by the original freshness event, not added as a compromise loss.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialPrivateCheckedFreshness
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedChain RawCtxFamilyFreshnessProxy PqxdhInitialParentStoppedHop
open PqxdhInitialBeaconAmbient PqxdhInitialStoppedDisclosure
variable {ι M P I D K X Response Shared Result Origin A N C ContextId Store : Type}
  {extra : OracleSpec ι} {S B : Nat}

open PqxdhInitialCheckedFreshness (checked_contains)

/-- The literal stopped source followed by its actual finite checker retains the original full-post disclosure invariant and every prior candidate. -/
theorem checked_invariant {A N C ContextId : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (continuation : PqxdhInitialParentStoppedHop.Continuation ContextId extra M P I D K X Response Shared A N C Result Origin S B)
    (context : ContextId × RawCtxSelectedParentEntry.Entry) (target : RootOutput) (output : PqxdhFullSecretInputKdf.FullOutput)
    (disclosed : List RatchetChain) (state : PqxdhInitialParentObserver.State A N C) (candidates : List RootOutput)
    (result : PqxdhInitialParentStoppedHop.Trace M P I D K A N C Result Origin S B)
    (supported : result ∈ support ((simulateQ
      (PqxdhInitialParentPrivateObserver.observed source writer (continuation.prior context.1) context.2 output
        (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
        (continuation.selector context.1) (continuation.aux context.1)
        (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target)
      (PqxdhInitialParentStoppedHop.program mark sender route decode continuation context)).run
        (initial disclosed (continuation.cut context.1) state candidates))) :
    PqxdhInitialDisclosureState.Invariant target disclosed result.1.1.2.1.roles.2 result.2 := by
  simp only [PqxdhInitialParentStoppedHop.program, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
    simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
  obtain ⟨completed, sourceReached, checked, checkerReached, rfl⟩ := supported
  rw [PqxdhInitialParentStoppedHop.baseProgram, ← QueryImpl.simulateQ_compose] at sourceReached
  have established := stopped_invariant target _
    (PqxdhInitialParentPrivateObserver.actual_rules source writer (continuation.prior context.1) context.2 output
      (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
      (continuation.selector context.1) (continuation.aux context.1) target)
    disclosed mark sender route decode (continuation.cut context.1) context.2.material _
    (initial_invariant target disclosed (continuation.cut context.1) state candidates) completed sourceReached
  have kept := PqxdhInitialDisclosureState.trace_keep _ _ _ _ (checker_quiet (continuation.depth context.1)) completed.2 checked checkerReached
  exact PqxdhInitialDisclosureState.invariant_keep target disclosed completed.1.2.1.roles.2 completed.2 checked.2 established kept


variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (continuation : Continuation ContextId extra M P I D K X Response Shared A N C Result Origin S B)
    (context : ContextId × RawCtxSelectedParentEntry.Entry) (target : RootOutput) (output : FullOutput)
    (disclosed : List RatchetChain) (state : PqxdhInitialParentObserver.State A N C) (candidates : List RootOutput)

noncomputable def nativeRun : ProbComp (Trace M P I D K A N C Result Origin S B) :=
  (simulateQ
    (PqxdhInitialParentPrivateObserver.observed source writer (continuation.prior context.1) context.2 output
      (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
      (continuation.selector context.1) (continuation.aux context.1)
      (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain target)) target)
    (program mark sender route decode continuation context)).run
      (initial disclosed (continuation.cut context.1) state candidates)

noncomputable def maskedRun : ProbComp (Trace M P I D K A N C Result Origin S B) :=
  (simulateQ
    (PqxdhInitialParentObserver.observed source writer (continuation.prior context.1) context.2 output
      (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
      (continuation.selector context.1) (continuation.aux context.1) RawCtxSelectedLiveRead.labelRead)
    (program mark sender route decode continuation context)).run
      (initial disclosed (continuation.cut context.1) state candidates)

/-- The complete source checker interprets its hidden and known slots as precisely the original byte freshness set, retaining every earlier ancestor. -/
theorem checked_fresh (earlier : List RatchetChain) (n : Nat) (depth : continuation.depth context.1 = some n)
    (result : Trace M P I D K A N C Result Origin S B)
    (supported : result ∈ support (nativeRun source writer mark sender route decode continuation context target output disclosed state candidates)) :
    RawCtxLiveLineage.Fresh (result.1.2.map (interpret (RawCtxFreshChainCut.concreteChain target)) ++ earlier)
      disclosed result.1.1.2.1.roles.2 ↔
    RawCtxLiveLineage.Fresh (RawCtxFreshChainCut.concreteChain target :: RawCtxFiniteLineageCheck.knownValues result.1.2 ++ earlier)
      disclosed result.1.1.2.1.roles.2 := by
  have hidden := checked_contains _ mark sender route decode continuation context n depth _ result supported
  unfold RawCtxLiveLineage.Fresh RawCtxLiveLineage.FreshValues
  apply forall_congr'
  intro value
  simp only [List.mem_append, List.mem_cons, RawCtxFiniteLineageCheck.interpreted_mem, hidden, and_true, or_assoc]

/-- Outside the same full candidate event, the actual final freshness predicate equals its target-free proxy using the literal saved history. -/
theorem checked_fresh_proxy (earlier : List RatchetChain) (n : Nat) (depth : continuation.depth context.1 = some n)
    (result : Trace M P I D K A N C Result Origin S B)
    (supported : result ∈ support (nativeRun source writer mark sender route decode continuation context target output disclosed state candidates))
    (safe : target ∉ result.2.1.2) :
    RawCtxLiveLineage.Fresh (result.1.2.map (interpret (RawCtxFreshChainCut.concreteChain target)) ++ earlier)
      disclosed result.1.1.2.1.roles.2 ↔
    Proxy (RawCtxFiniteLineageCheck.knownValues result.1.2 ++ earlier) disclosed result.1.1.2.1.roles.2 result.2.2 := by
  rw [checked_fresh source writer mark sender route decode continuation context target output disclosed state candidates earlier n depth result supported]
  have after := checked_invariant source writer mark sender route decode continuation context target output
    disclosed state candidates result supported
  exact fresh_proxy target _ disclosed result.1.1.2.1.roles.2 result.2.2 after.1
    (fun clear present => safe (after.2 clear present))


noncomputable def actualDecision (target : RootOutput) (earlier disclosed : List RatchetChain)
    (gate : Trace M P I D K A N C Result Origin S B → Prop)
    (result : Trace M P I D K A N C Result Origin S B) : Bool :=
  @decide (gate result ∧ RawCtxLiveLineage.Fresh
    (result.1.2.map (interpret (RawCtxFreshChainCut.concreteChain target)) ++ earlier)
      disclosed result.1.1.2.1.roles.2) (Classical.propDecidable _)

def remainingEvent (earlier disclosed : List RatchetChain)
    (gate : Trace M P I D K A N C Result Origin S B → Prop)
    (result : Trace M P I D K A N C Result Origin S B) : Prop :=
  gate result ∧ RawCtxLiveLineage.Fresh
    (RawCtxFiniteLineageCheck.knownValues result.1.2 ++ earlier) disclosed result.1.1.2.1.roles.2

private theorem event_distance {Value : Type} (work : ProbComp Value) (actual proxy bad : Value → Prop)
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

/-- The same original full-state gate and complete lineage differ from their proxy only at a recorded input alias on a clear-disclosure execution. -/
theorem good_bound (earlier : List RatchetChain)
    (gate : Trace M P I D K A N C Result Origin S B → Prop)
    (n : Nat) (depth : continuation.depth context.1 = some n) :
    let run := nativeRun source writer mark sender route decode continuation context target output disclosed state candidates
    |(Pr[fun result => gate result ∧ RawCtxLiveLineage.Fresh
      (result.1.2.map (interpret (RawCtxFreshChainCut.concreteChain target)) ++ earlier)
        disclosed result.1.1.2.1.roles.2 | run]).toReal -
      (Pr[fun result => gate result ∧ Proxy (RawCtxFiniteLineageCheck.knownValues result.1.2 ++ earlier)
        disclosed result.1.1.2.1.roles.2 result.2.2 | run]).toReal| ≤
      (Pr[fun result => target ∈ result.2.1.2 ∧ result.2.2 = false | run]).toReal := by
  apply event_distance
  case agreed =>
    intro result supported enabled safe
    exact ⟨enabled.1, (checked_fresh_proxy source writer mark sender route decode continuation context target output
      disclosed state candidates earlier n depth result supported (fun hit => safe ⟨hit, enabled.2.1⟩)).mpr enabled.2⟩
  case included =>
    intro result supported enabled
    have actual := (checked_fresh source writer mark sender route decode continuation context target output
      disclosed state candidates earlier n depth result supported).mp enabled.2
    exact ⟨enabled.1, fresh_clear _ _ disclosed _ _
      (checked_invariant source writer mark sender route decode continuation context target output
        disclosed state candidates result supported).1 actual,
      fun value present => actual value (List.mem_cons_of_mem _ present)⟩

/-- The Boolean source observation retains its publication gate and unconditioned original freshness event. -/
theorem decision_bound (earlier : List RatchetChain)
    (gate : Trace M P I D K A N C Result Origin S B → Prop)
    (n : Nat) (depth : continuation.depth context.1 = some n) :
    let run := nativeRun source writer mark sender route decode continuation context target output disclosed state candidates
    (actualDecision target earlier disclosed gate <$> run).boolDistAdvantage
      (decision (remainingEvent earlier disclosed gate) <$> run) ≤
      (Pr[fun result => target ∈ result.2.1.2 ∧ result.2.2 = false | run]).toReal := by
  simpa only [ProbComp.boolDistAdvantage, decision_probability, ← probEvent_eq_eq_probOutput,
    probEvent_map, Function.comp_def, actualDecision, decision, decide_eq_true_eq, remainingEvent, Proxy,
    and_assoc, and_left_comm, and_comm] using
      good_bound source writer mark sender route decode continuation context target output disclosed state candidates
        earlier gate n depth


/-- The exact full stopped program and its masked observer retain the same unconditioned gate and pay the complete original candidate event. -/
theorem proxy_bound (event : Trace M P I D K A N C Result Origin S B → Prop) :
    (decision event <$> nativeRun source writer mark sender route decode continuation context target output disclosed state candidates).boolDistAdvantage
      (decision event <$> maskedRun source writer mark sender route decode continuation context output disclosed state candidates) ≤
      (Pr[fun result => target ∈ result.2.1.2 |
        maskedRun source writer mark sender route decode continuation context output disclosed state candidates]).toReal := by
  let client := program mark sender route decode continuation context
  let initialState := initial disclosed (continuation.cut context.1) state candidates
  let partialMasked := (simulateQ
    (PqxdhInitialParentPrivateObserver.observed source writer (continuation.prior context.1) context.2 output
      (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
      (continuation.selector context.1) (continuation.aux context.1) RawCtxSelectedLiveRead.labelRead target)
    client).run initialState
  have agreement := PqxdhInitialParentPrivateObserver.event_good source writer (continuation.prior context.1) context.2 output
    (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
    (continuation.selector context.1) (continuation.aux context.1) target client initialState event
  rw [ProbComp.boolDistAdvantage, decision_probability, decision_probability, nativeRun, agreement]
  have variation := (abs_probOutput_toReal_sub_le_tvDist
    (decision event <$> partialMasked)
    (decision event <$> maskedRun source writer mark sender route decode continuation context output disclosed state candidates)).trans
      (tvDist_map_le (decision event) _ _)
  rw [decision_probability, decision_probability, tvDist_comm] at variation
  exact variation.trans (PqxdhInitialParentPrivateObserver.distance source writer (continuation.prior context.1) context.2 output
    (continuation.pre context.1) (continuation.application context.1) (continuation.initializer context.1)
    (continuation.selector context.1) (continuation.aux context.1) RawCtxSelectedLiveRead.labelRead target client initialState)

/-- Candidate aliases on clear-disclosure executions cost at most twice the same masked candidate event; forbidden disclosures add no compromise term. -/
theorem good_alias_bound :
    (Pr[fun result => target ∈ result.2.1.2 ∧ result.2.2 = false |
      nativeRun source writer mark sender route decode continuation context target output disclosed state candidates]).toReal ≤
      2 * (Pr[fun result => target ∈ result.2.1.2 |
        maskedRun source writer mark sender route decode continuation context output disclosed state candidates]).toReal := by
  have bound := proxy_bound source writer mark sender route decode continuation context target output disclosed state candidates
    (fun result => target ∈ result.2.1.2)
  simp only [ProbComp.boolDistAdvantage, decision_probability] at bound
  have contained := ENNReal.toReal_mono probEvent_ne_top (probEvent_mono
    (mx := maskedRun source writer mark sender route decode continuation context output disclosed state candidates)
    (fun result _ (hit : target ∈ result.2.1.2 ∧ result.2.2 = false) => hit.1))
  linarith [(abs_le.mp bound).2]

/-- The original complete source freshness observation differs from its target-free masked observer by at most three copies of the full candidate event, including the appended checker. -/
theorem bound (earlier : List RatchetChain)
    (gate : Trace M P I D K A N C Result Origin S B → Prop)
    (n : Nat) (depth : continuation.depth context.1 = some n) :
    (actualDecision target earlier disclosed gate <$>
      nativeRun source writer mark sender route decode continuation context target output disclosed state candidates).boolDistAdvantage
      (decision (remainingEvent earlier disclosed gate) <$>
        maskedRun source writer mark sender route decode continuation context output disclosed state candidates) ≤
      3 * (Pr[fun result => target ∈ result.2.1.2 |
        maskedRun source writer mark sender route decode continuation context output disclosed state candidates]).toReal := by
  have triangle := ProbComp.boolDistAdvantage_triangle
    (actualDecision target earlier disclosed gate <$>
      nativeRun source writer mark sender route decode continuation context target output disclosed state candidates)
    (decision (remainingEvent earlier disclosed gate) <$>
      nativeRun source writer mark sender route decode continuation context target output disclosed state candidates)
    (decision (remainingEvent earlier disclosed gate) <$>
      maskedRun source writer mark sender route decode continuation context output disclosed state candidates)
  have first := (decision_bound source writer mark sender route decode continuation context target output disclosed state candidates
    earlier gate n depth).trans
      (good_alias_bound source writer mark sender route decode continuation context target output disclosed state candidates)
  have second := proxy_bound source writer mark sender route decode continuation context target output disclosed state candidates
    (remainingEvent earlier disclosed gate)
  linarith

end BeaconcryptCore.Computational.PqxdhInitialPrivateCheckedFreshness

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateCheckedFreshness.checked_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateCheckedFreshness.checked_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateCheckedFreshness.checked_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateCheckedFreshness.checked_fresh

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateCheckedFreshness.checked_fresh_proxy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateCheckedFreshness.checked_fresh_proxy

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateCheckedFreshness.good_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateCheckedFreshness.good_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateCheckedFreshness.decision_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateCheckedFreshness.decision_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateCheckedFreshness.proxy_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateCheckedFreshness.proxy_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateCheckedFreshness.good_alias_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateCheckedFreshness.good_alias_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPrivateCheckedFreshness.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPrivateCheckedFreshness.bound

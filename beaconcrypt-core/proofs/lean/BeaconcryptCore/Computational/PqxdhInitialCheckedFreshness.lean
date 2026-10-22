import BeaconcryptCore.Computational.PqxdhInitialStoppedDisclosure

/-!
The actual complete stopped builder/post execution and its finite checker use the original byte-value freshness predicate, including prior disclosures and ancestors. The target-free proxy retains the same original publication gate and complete source result. Its discrepancy charges only input aliases on a clear-disclosure execution; actual forbidden reads are excluded by the original freshness event, not added as a compromise loss.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialCheckedFreshness
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedChain RawCtxFamilyFreshnessProxy PqxdhInitialParentStoppedHop
open PqxdhInitialBeaconAmbient PqxdhInitialStoppedDisclosure
variable {ι M P I D K X Response Shared Result Origin A N C ContextId Store : Type}
  {extra : OracleSpec ι} {S B : Nat}

/-- The actual appended checker retains the omitted input under every backend and full source continuation. -/
theorem checked_contains
    (backend : QueryImpl (PqxdhInitialParentObserverCompiler.Spec extra I D K X Response Shared) (StateT Store ProbComp))
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (continuation : Continuation ContextId extra M P I D K X Response Shared A N C Result Origin S B)
    (context : ContextId × RawCtxSelectedParentEntry.Entry) (n : Nat) (depth : continuation.depth context.1 = some n)
    (state : Store) (result : Final M P I D K Result Origin S B × Store)
    (supported : result ∈ support ((simulateQ backend (program mark sender route decode continuation context)).run state)) :
    Slot.hidden ∈ result.1.2 := by
  simp only [program, simulateQ_bind, StateT.run_bind, mem_support_bind_iff,
    simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
  obtain ⟨original, _, tail, reached, rfl⟩ := supported
  exact RawCtxFiniteLineageCheck.returned_contains RawCtxFiniteLineageCheck.labelKey
    (backend ∘ₛ checkerCompiler) n .hidden original.2 tail
    (by simpa only [depth, checker, QueryImpl.simulateQ_compose] using reached)

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (continuation : Continuation ContextId extra M P I D K X Response Shared A N C Result Origin S B)
    (context : ContextId × RawCtxSelectedParentEntry.Entry) (target : RootOutput) (output : FullOutput)
    (disclosed : List RatchetChain) (state : PqxdhInitialParentObserver.State A N C) (candidates : List RootOutput)

noncomputable def nativeRun : ProbComp (Trace M P I D K A N C Result Origin S B) :=
  (simulateQ
    (PqxdhInitialParentObserverAliases.observed source writer (continuation.prior context.1) context.2 output
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

/-- The same original full-state gate and complete lineage differ from their proxy only at a recorded input alias on a clear-disclosure execution. -/
theorem good_bound (earlier : List RatchetChain)
    (gate : Trace M P I D K A N C Result Origin S B → Prop)
    (n : Nat) (depth : continuation.depth context.1 = some n) :
    let run := nativeRun source writer mark sender route decode continuation context target output disclosed state candidates
    |(Pr{let result ← run}[gate result ∧ RawCtxLiveLineage.Fresh
      (result.1.2.map (interpret (RawCtxFreshChainCut.concreteChain target)) ++ earlier)
        disclosed result.1.1.2.1.roles.2]).toReal -
      (Pr{let result ← run}[gate result ∧ Proxy (RawCtxFiniteLineageCheck.knownValues result.1.2 ++ earlier)
        disclosed result.1.1.2.1.roles.2 result.2.2]).toReal| ≤
      (Pr{let result ← run}[target ∈ result.2.1.2 ∧ result.2.2 = false]).toReal := by
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

set_option backward.isDefEq.respectTransparency false in
/-- The Boolean source observation retains its publication gate and unconditioned original freshness event. -/
theorem decision_bound (earlier : List RatchetChain)
    (gate : Trace M P I D K A N C Result Origin S B → Prop)
    (n : Nat) (depth : continuation.depth context.1 = some n) :
    let run := nativeRun source writer mark sender route decode continuation context target output disclosed state candidates
    (actualDecision target earlier disclosed gate <$> run).boolDistance
      (decision (remainingEvent earlier disclosed gate) <$> run) ≤
      (Pr{let result ← run}[target ∈ result.2.1.2 ∧ result.2.2 = false]).toReal := by
  dsimp only
  simp only [ProbComp.boolDistance]
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true, decision_probability, prEvent_map]
  simpa only [actualDecision, decide_eq_true_eq, decision, remainingEvent, Proxy, and_assoc, and_left_comm,
    and_comm] using
      good_bound source writer mark sender route decode continuation context target output disclosed state candidates
        earlier gate n depth


set_option backward.isDefEq.respectTransparency false in
/-- The exact full stopped program and its masked observer retain the same unconditioned gate and pay the complete original candidate event. -/
theorem proxy_bound (event : Trace M P I D K A N C Result Origin S B → Prop) :
    (decision event <$> nativeRun source writer mark sender route decode continuation context target output disclosed state candidates).boolDistance
      (decision event <$> maskedRun source writer mark sender route decode continuation context output disclosed state candidates) ≤
      (Pr{let result ← maskedRun source writer mark sender route decode continuation context output disclosed state candidates}[target ∈ result.2.1.2]).toReal := by
  have bound := local_bound source writer mark sender route decode
    { continuation with
      initial := (fun _ => initial disclosed (continuation.cut context.1) state candidates)
      event := (fun _ => event) } context target output
  simpa only [privateGame, observer, observed, bad, PqxdhInitialParentStoppedHop.candidates,
    program, baseProgram, nativeRun, maskedRun, prEvent_map, decide_eq_true_eq] using bound

/-- Candidate aliases on clear-disclosure executions cost at most twice the same masked candidate event; forbidden disclosures add no compromise term. -/
theorem good_alias_bound :
    (Pr{let result ← nativeRun source writer mark sender route decode continuation context target output disclosed state candidates}[target ∈ result.2.1.2 ∧ result.2.2 = false]).toReal ≤
      2 * (Pr{let result ← maskedRun source writer mark sender route decode continuation context output disclosed state candidates}[target ∈ result.2.1.2]).toReal := by
  have bound := proxy_bound source writer mark sender route decode continuation context target output disclosed state candidates
    (fun result => target ∈ result.2.1.2)
  simp only [ProbComp.boolDistance] at bound
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true, decision_probability,
    decision_probability] at bound
  have contained := ENNReal.toReal_mono (prEvent_ne_top _) (prEvent_mono_of_support
    (mx := maskedRun source writer mark sender route decode continuation context output disclosed state candidates)
    (p := fun result => target ∈ result.2.1.2 ∧ result.2.2 = false) (q := fun result => target ∈ result.2.1.2)
    (fun result _ (hit : target ∈ result.2.1.2 ∧ result.2.2 = false) => hit.1))
  linarith [(abs_le.mp bound).2]

/-- The original complete source freshness observation differs from its target-free masked observer by at most three copies of the full candidate event, including the appended checker. -/
theorem bound (earlier : List RatchetChain)
    (gate : Trace M P I D K A N C Result Origin S B → Prop)
    (n : Nat) (depth : continuation.depth context.1 = some n) :
    (actualDecision target earlier disclosed gate <$>
      nativeRun source writer mark sender route decode continuation context target output disclosed state candidates).boolDistance
      (decision (remainingEvent earlier disclosed gate) <$>
        maskedRun source writer mark sender route decode continuation context output disclosed state candidates) ≤
      3 * (Pr{let result ← maskedRun source writer mark sender route decode continuation context output disclosed state candidates}[target ∈ result.2.1.2]).toReal := by
  have triangle := ProbComp.boolDistance_triangle
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

end BeaconcryptCore.Computational.PqxdhInitialCheckedFreshness

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCheckedFreshness.checked_contains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCheckedFreshness.checked_contains

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCheckedFreshness.checked_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCheckedFreshness.checked_fresh

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCheckedFreshness.checked_fresh_proxy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCheckedFreshness.checked_fresh_proxy

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCheckedFreshness.good_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCheckedFreshness.good_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCheckedFreshness.decision_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCheckedFreshness.decision_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCheckedFreshness.proxy_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCheckedFreshness.proxy_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCheckedFreshness.good_alias_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCheckedFreshness.good_alias_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCheckedFreshness.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCheckedFreshness.bound

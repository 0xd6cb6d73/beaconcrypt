import BeaconcryptCore.Computational.RawCtxFamilyPendingCompiler

/-!
A selected record continues inside an original non-read family operation. This prefix retains its full optional result and family state, all earlier candidates and the unchanged direct-read flag. The original outside LIVE client then resumes after its one history tick. Its final freshness invariant is derived from this exact prefix and actual outside source schedule, without assuming a final history correspondence or excluding public guesses from freshness.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxFamilyCompletionFreshness
open RawCtxFamilySourceFreshness RawCtxFamilyFreshnessProxy RawCtxFamilyPendingCompiler
open PqxdhSecretInputKdf RawCtxSelectedChain
variable {M P I D K A Result Value : Type} {S B : Nat}

/-- The complete non-read prefix preserves its direct-read flag and every earlier available-input candidate, including on unsuccessful operations. -/
theorem prefix_state (parameters : Parameters) (work : OracleComp PrimitiveSpec Result)
    (state : RawCtxSelectedParentLive.State A) (result : Result × RawCtxSelectedParentLive.State A)
    (supported : result ∈ support ((simulateQ (observed parameters)
      (simulateQ RawCtxSelectedLiveCompiler.primitiveForward work)).run state)) :
    result.2.2 = state.2 ∧ state.1.2 ⊆ result.2.1.2 := by
  have keep := RawCtxFamilyReadCompiler.retained_candidates (handler parameters) _ state result supported
  have same := RawCtxFamilyReadCompiler.primitive_complete (handler (A := A) parameters) work state.1 state.2
  change _ = (simulateQ (observed parameters) (simulateQ RawCtxSelectedLiveCompiler.primitiveForward work)).run state at same
  rw [← same, support_map] at supported
  obtain ⟨reply, reached, rfl⟩ := supported
  exact ⟨rfl, keep⟩

def initial (prior : List RatchetChain) (history : RawCtxProtocolReveals.History S B)
    (state : RawCtxSharedPrimitive.SharedState A) (candidates : List RootOutput) : RawCtxSelectedParentLive.State A :=
  ((state, knownInputs prior history ++ candidates), false)

/-- Every supported completion and original outside LIVE execution derives its final disclosure witness and candidate inclusion from the actual initial history. -/
theorem completion_invariant (parameters : Parameters) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (prior : List RatchetChain) (history : RawCtxProtocolReveals.History S B)
    (outside : Value → OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (work : OracleComp PrimitiveSpec (Value × Roles M P I D K S B))
    (state : RawCtxSharedPrimitive.SharedState A) (candidates : List RootOutput)
    (result : (Result × State M P I D K S B) × RawCtxSelectedParentLive.State A)
    (supported : result ∈ support ((simulateQ (observed parameters)
      (completion sender route decode history outside work)).run (initial prior history state candidates))) :
    Invariant parameters.target prior (result.1.2, result.2) := by
  simp only [completion, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨finished, prefixReached, tailReached⟩ := supported
  have kept := prefix_state parameters work (initial prior history state candidates) finished prefixReached
  have before : Invariant parameters.target prior
      ((finished.1.2, RawCtxProtocolReveals.tick history), finished.2) := by
    constructor
    · intro impossible
      simp only [initial] at kept
      rw [kept.1] at impossible
      cases impossible
    · intro _ value present
      exact kept.2 (List.mem_append_left candidates present)
  apply schedule_invariant parameters calls publicCalls sender route decode prior (outside finished.1.1)
    ((finished.1.2, RawCtxProtocolReveals.tick history), finished.2) before (result.1.1, (result.1.2, result.2))
  rw [← source_project, support_map]
  exact ⟨result, tailReached, rfl⟩

/-- Outside the same full candidate event, the actual selected completion's byte freshness equals the executable proxy. -/
theorem completion_fresh_proxy (parameters : Parameters) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (blocked prior : List RatchetChain) (history : RawCtxProtocolReveals.History S B)
    (outside : Value → OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (work : OracleComp PrimitiveSpec (Value × Roles M P I D K S B))
    (state : RawCtxSharedPrimitive.SharedState A) (candidates : List RootOutput)
    (result : (Result × State M P I D K S B) × RawCtxSelectedParentLive.State A)
    (supported : result ∈ support ((simulateQ (observed parameters)
      (completion sender route decode history outside work)).run (initial prior history state candidates)))
    (safe : parameters.target ∉ result.2.1.2) :
    RawCtxLiveLineage.Fresh (RawCtxFreshChainCut.concreteChain parameters.target :: blocked) prior result.1.2.2 ↔
      Proxy blocked prior result.1.2.2 result.2.2 := by
  have after := completion_invariant parameters sender route decode prior history outside work state candidates result supported
  exact fresh_proxy parameters.target blocked prior result.1.2.2 result.2.2 after.1
    (fun clear present => safe (after.2 clear present))

private theorem event_distance {Result : Type} (work : ProbComp Result) (actual proxy bad : Result → Prop)
    (included : ∀ result ∈ support work, actual result → proxy result)
    (agreed : ∀ result ∈ support work, proxy result → ¬ bad result → actual result) :
    |(Pr[actual | work]).toReal - (Pr[proxy | work]).toReal| ≤ (Pr[bad | work]).toReal := by
  have smaller : Pr[actual | work] ≤ Pr[proxy | work] := probEvent_mono included
  have covered : Pr[proxy | work] ≤ Pr[fun result => actual result ∨ bad result | work] := by
    apply probEvent_mono
    intro result supported enabled
    by_cases hit : bad result
    · exact Or.inr hit
    · exact Or.inl (agreed result supported enabled hit)
  have larger : Pr[proxy | work] ≤ Pr[actual | work] + Pr[bad | work] :=
    covered.trans (probEvent_or_le work actual bad)
  have smallerReal := ENNReal.toReal_mono probEvent_ne_top smaller
  have largerReal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩) larger
  rw [ENNReal.toReal_add probEvent_ne_top probEvent_ne_top] at largerReal
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr smallerReal)]
  linarith

/-- The complete in-progress source continuation changes from actual freshness to its target-free proxy by at most its original final candidate event, with no disclosure probability added. -/
theorem completion_event_bound (parameters : Parameters) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (blocked prior : List RatchetChain) (history : RawCtxProtocolReveals.History S B)
    (outside : Value → OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool)
    (work : OracleComp PrimitiveSpec (Value × Roles M P I D K S B))
    (state : RawCtxSharedPrimitive.SharedState A) (candidates : List RootOutput) :
    let execution := (simulateQ (observed parameters) (completion sender route decode history outside work)).run
      (initial prior history state candidates)
    |(Pr[fun result => result.1.1 = true ∧ RawCtxLiveLineage.Fresh
        (RawCtxFreshChainCut.concreteChain parameters.target :: blocked) prior result.1.2.2 | execution]).toReal -
      (Pr[fun result => result.1.1 = true ∧ Proxy blocked prior result.1.2.2 result.2.2 | execution]).toReal| ≤
      (Pr[fun result => parameters.target ∈ result.2.1.2 | execution]).toReal := by
  apply event_distance
  · intro result supported enabled
    have after := completion_invariant parameters sender route decode prior history outside work state candidates result supported
    exact ⟨enabled.1, fresh_clear _ blocked prior _ _ after.1 enabled.2,
      fun value present => enabled.2 value (List.mem_cons_of_mem _ present)⟩
  · intro result supported enabled safe
    exact ⟨enabled.1, (completion_fresh_proxy parameters sender route decode blocked prior history outside work
      state candidates result supported safe).mpr enabled.2⟩

/-- The bound consumes the actual reached material-only Context.stopped program, including its pending owner, Server or Beacon, family publication and unchanged outer LIVE client. -/
theorem stopped_event_bound (parameters : Parameters) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (blocked prior : List RatchetChain) (request : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (history : RawCtxProtocolReveals.History S B)
    (outside : (RawCtxProtocolRoles.SourceSpec S B).Range request → OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool)
    (inner : RawCtxSelectedFamilyContext.FamilyContext M P I D K
      ((RawCtxProtocolRoles.SourceSpec S B).Range request) S B) (value : PqxdhOrderedChainHybrids.Material)
    (state : RawCtxSharedPrimitive.SharedState A) (candidates : List RootOutput) :
    let execution := (simulateQ (observed parameters) (simulateQ live
      (RawCtxSelectedFamilyContext.stopped sender route decode (.family request history outside inner) value))).run
      (initial prior history state candidates)
    |(Pr[fun result => result.1.1 = true ∧ RawCtxLiveLineage.Fresh
        (RawCtxFreshChainCut.concreteChain parameters.target :: blocked) prior result.1.2.2 | execution]).toReal -
      (Pr[fun result => result.1.1 = true ∧ Proxy blocked prior result.1.2.2 result.2.2 | execution]).toReal| ≤
      (Pr[fun result => parameters.target ∈ result.2.1.2 | execution]).toReal := by
  dsimp only
  rw [stopped_source]
  exact completion_event_bound parameters sender route decode blocked prior history outside _ state candidates

/-- The initial candidate ledger explicitly charges every earlier candidate and every actual prior/history disclosed value, with duplicates retained. -/
theorem initial_length (prior : List RatchetChain) (history : RawCtxProtocolReveals.History S B)
    (state : RawCtxSharedPrimitive.SharedState A) (candidates : List RootOutput) :
    (initial prior history state candidates).1.2.length =
      (RawCtxLiveLineage.known prior history).length + candidates.length := by
  simp only [initial, List.length_append, knownInputs, List.length_map]

end BeaconcryptCore.Computational.RawCtxFamilyCompletionFreshness

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyCompletionFreshness.prefix_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyCompletionFreshness.prefix_state

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyCompletionFreshness.completion_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyCompletionFreshness.completion_invariant

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyCompletionFreshness.completion_fresh_proxy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyCompletionFreshness.completion_fresh_proxy

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyCompletionFreshness.completion_event_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyCompletionFreshness.completion_event_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyCompletionFreshness.stopped_event_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyCompletionFreshness.stopped_event_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyCompletionFreshness.initial_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyCompletionFreshness.initial_length

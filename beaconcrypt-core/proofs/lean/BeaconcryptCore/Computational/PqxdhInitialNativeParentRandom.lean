import BeaconcryptCore.Computational.PqxdhInitialNativeLineageCheck
import BeaconcryptCore.Computational.PqxdhInitialNativeParentChild
import BeaconcryptCore.Computational.PqxdhInitialNativeParentChecked

/-!
The deferred full76 child draw retains the original source publication and complete byte-level lineage freshness. The appended checker reads the already cached published path before private bookkeeping is projected. Its retained early-child view then realizes the same partial-routing observer as the real endpoint, with the original initializer and every ambient callback unchanged.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialNativeParentRandom
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids
open PqxdhInitialNativeLog PqxdhInitialNativeResponse PqxdhInitialNativeRetained
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedParentPrivatePatch RawCtxCursorLineage RawCtxSelectiveChainGame
variable {ι M P I D K X Response Shared A N C Result : Type} {extra : OracleSpec ι} {S B : Nat}

/-- The early child insertion preserves every existing binding when its address is absent; the complete previous root walk is retained. -/
theorem child_extends (table : RawCtxKdfRequestTable.Table) (target : RootOutput) (output : FullOutput)
    (missing : table (targetAddress target) = none) :
    Extends table (table.cacheQuery (targetAddress target) output) := by
  intro request response found
  by_cases same : request = targetAddress target
  · subst request
    rw [missing] at found
    cases found
  · exact (QueryCache.cacheQuery_of_ne (spec := JointKdfRO) table output same).trans found

/-- The retained early-child view gives the literal original-root freshness event, split at its actual cached parent walk. -/
theorem retained_fresh (source : FixedHkdfSha512NoSaltSource) (state : State A N C)
    (address : JointKdfAddress) (parent output : FullOutput)
    (missing : state.1.1.2.1 address = none) (matching : matched state.1.1.2.2 address = true)
    (childMissing : state.1.1.2.1 (targetAddress (nextChain parent)) = none)
    (separate : targetAddress (nextChain parent) ≠ address)
    (root : RootOutput) (earlier : List RootOutput)
    (walked : walk state.1.1.2.1 state.1.1.2.2.depth root = some (earlier, state.1.1.2.2.input))
    (number : Std.U64) (remaining : Nat) (position : number.val = (state.1.1.2.2.depth + 1) + remaining + 1)
    (ancestors disclosed : List RatchetChain) (history : RawCtxProtocolReveals.History S B) :
    RawCtxLiveLineage.Fresh
      (RawCtxPublishedLineage.lineage
        (view (productionStream source.crypto)
          ((updated address parent state).1.1.2.1.cacheQuery (targetAddress (nextChain parent)) output))
        (RawCtxFreshChainCut.concreteChain root) (number.val - 1) ++ ancestors) disclosed history ↔
    RawCtxLiveLineage.Fresh
      ((PqxdhInitialParentStoppedHop.checkerTrace (view (productionStream source.crypto) state.1.1.2.1)
        (fromOutput address parent) (nextChain parent) output (some remaining)).map
        (RawCtxSelectedChain.interpret (RawCtxFreshChainCut.concreteChain (nextChain parent))) ++
        ((earlier ++ [state.1.1.2.2.input]).map RawCtxFreshChainCut.concreteChain ++ ancestors)) disclosed history := by
  have childAbsent : (updated address parent state).1.1.2.1 (targetAddress (nextChain parent)) = none := by
    simpa only [updated, QueryCache.cacheQuery_of_ne (spec := JointKdfRO) _ parent separate] using childMissing
  have splitting := RawCtxPublishedLineage.fresh_split (productionStream source.crypto)
    (updated address parent state).1.1.2.1 _ (child_extends _ _ output childAbsent)
    (state.1.1.2.2.depth + 1) remaining root (earlier ++ [state.1.1.2.2.input], nextChain parent)
    (PqxdhInitialNativeParentEvent.parent_walk state address parent missing matching root earlier walked)
    ancestors disclosed history
  have index : number.val - 1 = (state.1.1.2.2.depth + 1) + remaining := by omega
  rw [index, splitting, PqxdhInitialNativeParentChild.child_view source state address parent output separate]
  have checker := RawCtxFiniteLineageCheck.native_trace (view (productionStream source.crypto) state.1.1.2.1)
    (fromOutput address parent) (nextChain parent) output separate remaining .hidden
  exact congrArg (fun values => RawCtxLiveLineage.Fresh
    (values ++ ((earlier ++ [state.1.1.2.2.input]).map RawCtxFreshChainCut.concreteChain ++ ancestors)) disclosed history)
    checker |>.symm |>.to_iff

noncomputable def retainedDecision (prior : Prior) (root : RootOutput)
    (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (ancestors disclosed : List RatchetChain)
    (result : Bool × PqxdhInitialOriginPostPath.Snapshot M P I D K S B) : Bool :=
  @decide (PqxdhInitialPublishedEvent.Gate selected number result ∧ RawCtxLiveLineage.Fresh
    (RawCtxPublishedLineage.lineage prior (RawCtxFreshChainCut.concreteChain root) (number.val - 1) ++ ancestors)
    disclosed result.2.1.roles.2) (Classical.propDecidable _)

/-- The random source endpoint preserves the original publication and complete final-table freshness through the deferred draw. Its cache premise is only actual supported publication, never an assumed final-game equality. -/
theorem source_random (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N PqxdhCorrelatedExpand.RootOracle.QueryCache))
    (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B)
      (Bool × PqxdhInitialOriginPostPath.Snapshot M P I D K S B))
    (state : State A N PqxdhCorrelatedExpand.RootOracle.QueryCache)
    (missing : state.1.1.2.1 (cursorAddress state.1.1.2.2) = none)
    (root : RootOutput) (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (positive : 0 < number.val) (ancestors disclosed : List RatchetChain)
    (published : ∀ result ∈ support ((simulateQ (handler source writer (state.1.1.2.2.depth + 1) external) client).run state),
      PqxdhInitialPublishedEvent.Gate selected number result.1 →
        RawCtxSourcePublishedPath.Cached root number result.2.1.1.2.1) :
    𝒟[PqxdhInitialPublishedEvent.sourceDecision source root selected number ancestors disclosed <$>
      (simulateQ (handler source writer (state.1.1.2.2.depth + 1) external) client).run state] =
    𝒟[($ᵗ FullOutput) >>= fun output =>
      let prior := view (productionStream source.crypto) (state.1.1.2.1.cacheQuery (cursorAddress state.1.1.2.2) output)
      (fun result => retainedDecision prior root selected number ancestors disclosed result.1) <$>
        (simulateQ (retained source writer prior external) client).run (project state)] := by
  classical
  let gate := fun result : Bool × PqxdhInitialOriginPostPath.Snapshot M P I D K S B =>
    decide (PqxdhInitialPublishedEvent.Gate selected number result)
  let observe := fun result : ((Bool × PqxdhInitialOriginPostPath.Snapshot M P I D K S B) × Option (List RatchetChain)) ×
      RetainedState A N PqxdhCorrelatedExpand.RootOracle.QueryCache =>
    match result.1.2 with
    | none => false
    | some values => decide (PqxdhInitialPublishedEvent.Gate selected number result.1.1 ∧
        RawCtxLiveLineage.Fresh (values ++ ancestors) disclosed result.1.1.2.1.roles.2)
  have cached : ∀ result ∈ support ((simulateQ (handler source writer (state.1.1.2.2.depth + 1) external) client).run state),
      gate result.1 = true → ∃ path, walk result.2.1.1.2.1 (number.val - 1 + 1) root = some path := by
    intro result reached good
    obtain ⟨earlier, input, walked⟩ := published result reached (of_decide_eq_true good)
    exact ⟨(earlier, input), by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ number.val)] using walked⟩
  have equality := EvalDistEq.map
    (PqxdhInitialNativeLineageCheck.logged_uniform source writer external client gate (number.val - 1) root state missing cached)
    observe
  simp only [Functor.map_map, map_bind] at equality
  have observed : ∀ (prior : Prior) (result : Bool × PqxdhInitialOriginPostPath.Snapshot M P I D K S B)
      (ambient : RetainedState A N PqxdhCorrelatedExpand.RootOracle.QueryCache),
      observe ((result, if gate result then some
        (RawCtxFiniteLineageCheck.trace RawCtxFiniteLineageCheck.nativeKey (RawCtxPublishedLineage.step prior)
          (number.val - 1) (RawCtxFreshChainCut.concreteChain root)) else none), ambient) =
      retainedDecision prior root selected number ancestors disclosed result := by
    intro prior result ambient
    by_cases good : PqxdhInitialPublishedEvent.Gate selected number result
    · simp only [observe, gate, good, decide_true, ite_true, retainedDecision, RawCtxPublishedLineage.lineage]
    · simp only [observe, gate, good, decide_false, Bool.false_eq_true, ite_false, retainedDecision, false_and, decide_false]
  simp only [observed] at equality
  exact equality.evalDist_eq

/-- The original selected parent response advances the source cursor to the exact native child address. -/
theorem child_cursor (state : State A N C) (address : JointKdfAddress) (parent : FullOutput)
    (matching : matched state.1.1.2.2 address = true) :
    cursorAddress (updated address parent state).1.1.2.2 = targetAddress (nextChain parent) := by
  simp only [updated, advance, matching, ite_true, cursorAddress]
  exact (PqxdhInitialNativeLineageCheck.request_concrete (nextChain parent)).symm

/-- The same original full result has precisely the partial observer's native freshness decision after the early child draw. -/
theorem retained_decision (source : FixedHkdfSha512NoSaltSource) (state : State A N C)
    (address : JointKdfAddress) (parent output : FullOutput)
    (missing : state.1.1.2.1 address = none) (matching : matched state.1.1.2.2 address = true)
    (childMissing : state.1.1.2.1 (targetAddress (nextChain parent)) = none)
    (separate : targetAddress (nextChain parent) ≠ address)
    (root : RootOutput) (earlier : List RootOutput)
    (walked : walk state.1.1.2.1 state.1.1.2.2.depth root = some (earlier, state.1.1.2.2.input))
    (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (remaining : Nat)
    (position : number.val = (state.1.1.2.2.depth + 1) + remaining + 1)
    (ancestors disclosed : List RatchetChain)
    (result : Bool × PqxdhInitialOriginPostPath.Snapshot M P I D K S B) :
    retainedDecision (view (productionStream source.crypto)
      ((updated address parent state).1.1.2.1.cacheQuery (targetAddress (nextChain parent)) output))
      root selected number ancestors disclosed result =
    PqxdhInitialNativeParentEvent.nativeDecision (view (productionStream source.crypto) state.1.1.2.1)
      (fromOutput address parent) (nextChain parent) output remaining
      ((earlier ++ [state.1.1.2.2.input]).map RawCtxFreshChainCut.concreteChain) ancestors disclosed selected number result := by
  apply Bool.eq_iff_iff.mpr
  simp only [retainedDecision, PqxdhInitialNativeParentEvent.nativeDecision, decide_eq_true_eq]
  exact and_congr_right (fun _ => retained_fresh source state address parent output missing matching childMissing
    separate root earlier walked number remaining position ancestors disclosed result.2.1.roles.2)

/-- The actual later source stage after its fresh parent draw equals an early full child draw with the identical native publication/freshness decision. -/
theorem parent_random (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N PqxdhCorrelatedExpand.RootOracle.QueryCache))
    (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B)
      (Bool × PqxdhInitialOriginPostPath.Snapshot M P I D K S B))
    (state : State A N PqxdhCorrelatedExpand.RootOracle.QueryCache) (address : JointKdfAddress) (parent : FullOutput)
    (missing : state.1.1.2.1 address = none) (matching : matched state.1.1.2.2 address = true)
    (childMissing : state.1.1.2.1 (targetAddress (nextChain parent)) = none)
    (separate : targetAddress (nextChain parent) ≠ address)
    (root : RootOutput) (earlier : List RootOutput)
    (walked : walk state.1.1.2.1 state.1.1.2.2.depth root = some (earlier, state.1.1.2.2.input))
    (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (remaining : Nat)
    (position : number.val = (state.1.1.2.2.depth + 1) + remaining + 1)
    (ancestors disclosed : List RatchetChain)
    (published : ∀ result ∈ support ((simulateQ (handler source writer (state.1.1.2.2.depth + 2) external) client).run
        (updated address parent state)),
      PqxdhInitialPublishedEvent.Gate selected number result.1 →
        RawCtxSourcePublishedPath.Cached root number result.2.1.1.2.1) :
    𝒟[PqxdhInitialPublishedEvent.sourceDecision source root selected number ancestors disclosed <$>
      (simulateQ (handler source writer (state.1.1.2.2.depth + 2) external) client).run (updated address parent state)] =
    𝒟[($ᵗ FullOutput) >>= fun output =>
      (fun result => PqxdhInitialNativeParentEvent.nativeDecision (view (productionStream source.crypto) state.1.1.2.1)
        (fromOutput address parent) (nextChain parent) output remaining
        ((earlier ++ [state.1.1.2.2.input]).map RawCtxFreshChainCut.concreteChain) ancestors disclosed selected number result.1) <$>
      (simulateQ (retained source writer
        (view (productionStream source.crypto)
          ((updated address parent state).1.1.2.1.cacheQuery (targetAddress (nextChain parent)) output)) external) client).run
          (project state)] := by
  have childAbsent : (updated address parent state).1.1.2.1
      (cursorAddress (updated address parent state).1.1.2.2) = none := by
    rw [child_cursor state address parent matching]
    simpa only [updated, QueryCache.cacheQuery_of_ne (spec := JointKdfRO) _ parent separate] using childMissing
  have stage : (updated address parent state).1.1.2.2.depth + 1 = state.1.1.2.2.depth + 2 := by
    simp only [updated, advance, matching, ite_true, Nat.add_assoc]
  have equality := source_random source writer external client (updated address parent state) childAbsent root selected number
    (by omega) ancestors disclosed (by simpa only [stage] using published)
  rw [stage, child_cursor state address parent matching] at equality
  simp only [retained_decision source state address parent _ missing matching childMissing separate root earlier walked
    selected number remaining position ancestors disclosed] at equality
  exact equality

section Frame
open PqxdhInitialBeaconAmbient PqxdhInitialNativeParentRealization
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared)
    (Ambient A N PqxdhCorrelatedExpand.RootOracle.QueryCache))
  (application : Response → Ambient A N PqxdhCorrelatedExpand.RootOracle.QueryCache (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N PqxdhCorrelatedExpand.RootOracle.QueryCache
    PqxdhInitialNativeAudit.InitialReply)
  (selector : QueryImpl extra (Ambient A N PqxdhCorrelatedExpand.RootOracle.QueryCache))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N PqxdhCorrelatedExpand.RootOracle.QueryCache))
  (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (context : PqxdhInitialOriginContext.Context extra M P I D K Bool Bool S B) (parent : FullOutput)
  (state : State A N PqxdhCorrelatedExpand.RootOracle.QueryCache)
  (missing : state.1.1.2.1 (PqxdhInitialBuilderContext.address context.original) = none)
  (matching : matched state.1.1.2.2 (PqxdhInitialBuilderContext.address context.original) = true)
  (childMissing : state.1.1.2.1 (targetAddress (nextChain parent)) = none)
  (separate : targetAddress (nextChain parent) ≠ PqxdhInitialBuilderContext.address context.original)
  (root : RootOutput) (earlier : List RootOutput)
  (walked : walk state.1.1.2.1 state.1.1.2.2.depth root = some (earlier, state.1.1.2.2.input))
  (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (remaining : Nat)
  (position : number.val = (state.1.1.2.2.depth + 1) + remaining + 1)
  (ancestors disclosed : List RatchetChain)

include missing matching childMissing separate walked position in
/-- The complete randomized source continuation and source freshness event are exactly the same actual partial-routing observer with a full76 independent child. -/
theorem frame_random
    (published : ∀ result ∈ support ((simulateQ (handler source writer (state.1.1.2.2.depth + 2)
      (PqxdhInitialNativeAudit.external pre application initial selector aux))
      ((PqxdhInitialOriginContext.frame mark sender route decode context).2
        (PqxdhInitialParentBuilderContext.reply sender route decode context.original parent))).run
          (updated (PqxdhInitialBuilderContext.address context.original) parent state)),
      PqxdhInitialPublishedEvent.Gate selected number result.1 →
        RawCtxSourcePublishedPath.Cached root number result.2.1.1.2.1) :
    𝒟[PqxdhInitialPublishedEvent.sourceDecision source root selected number ancestors disclosed <$>
      (simulateQ (handler source writer (state.1.1.2.2.depth + 2)
        (PqxdhInitialNativeAudit.external pre application initial selector aux))
        ((PqxdhInitialOriginContext.frame mark sender route decode context).2
          (PqxdhInitialParentBuilderContext.reply sender route decode context.original parent))).run
            (updated (PqxdhInitialBuilderContext.address context.original) parent state)] =
    𝒟[($ᵗ FullOutput) >>= fun output =>
      (fun result => PqxdhInitialNativeParentEvent.nativeDecision (view (productionStream source.crypto) state.1.1.2.1)
        (fromOutput (PqxdhInitialBuilderContext.address context.original) parent) (nextChain parent) output remaining
        ((earlier ++ [state.1.1.2.2.input]).map RawCtxFreshChainCut.concreteChain) ancestors disclosed selected number
        (Prod.map id (Prod.map (PqxdhInitialParentPost.mapFront (RawCtxSelectedParentCalls.nativeKernel (nextChain parent))) id)
          result.1)) <$>
      (simulateQ (PqxdhInitialParentPrivateObserver.handler source writer (view (productionStream source.crypto) state.1.1.2.1)
        (fromOutput (PqxdhInitialBuilderContext.address context.original) parent) output pre application initial selector aux
        (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain (nextChain parent))) (nextChain parent))
        (simulateQ PqxdhInitialParentObserverCompiler.compiler
          (PqxdhInitialOriginContext.stopped mark sender route decode context (material parent)))).run (nested (project state))] := by
  rw [parent_random source writer (PqxdhInitialNativeAudit.external pre application initial selector aux)
    ((PqxdhInitialOriginContext.frame mark sender route decode context).2
      (PqxdhInitialParentBuilderContext.reply sender route decode context.original parent)) state
    (PqxdhInitialBuilderContext.address context.original) parent missing matching childMissing separate root earlier walked
    selected number remaining position ancestors disclosed published]
  apply EvalDistEq.evalDist_eq
  refine EvalDistEq.bind_right ($ᵗ FullOutput) fun output => ?_
  rw [PqxdhInitialNativeParentChild.retained_compiled source writer pre application initial selector aux
    mark sender route decode context parent output state separate]
  simp only [Functor.map_map]
  exact EvalDistEq.rfl

include missing matching separate walked position in
/-- The complete real source continuation uses the same original publication/freshness decision as the actual partial-routing observer. -/
theorem frame_real
    (published : ∀ result ∈ support ((simulateQ (handler source writer (state.1.1.2.2.depth + 1)
      (PqxdhInitialNativeAudit.external pre application initial selector aux))
      ((PqxdhInitialOriginContext.frame mark sender route decode context).2
        (PqxdhInitialParentBuilderContext.reply sender route decode context.original parent))).run
          (updated (PqxdhInitialBuilderContext.address context.original) parent state)),
      PqxdhInitialPublishedEvent.Gate selected number result.1 →
        RawCtxSourcePublishedPath.Cached root number result.2.1.1.2.1) :
    PqxdhInitialPublishedEvent.sourceDecision source root selected number ancestors disclosed <$>
      (simulateQ (handler source writer (state.1.1.2.2.depth + 1)
        (PqxdhInitialNativeAudit.external pre application initial selector aux))
        ((PqxdhInitialOriginContext.frame mark sender route decode context).2
          (PqxdhInitialParentBuilderContext.reply sender route decode context.original parent))).run
            (updated (PqxdhInitialBuilderContext.address context.original) parent state) =
    (fun result => PqxdhInitialNativeParentEvent.nativeDecision (view (productionStream source.crypto) state.1.1.2.1)
      (fromOutput (PqxdhInitialBuilderContext.address context.original) parent) (nextChain parent)
      (view (productionStream source.crypto) state.1.1.2.1 (targetAddress (nextChain parent))) remaining
      ((earlier ++ [state.1.1.2.2.input]).map RawCtxFreshChainCut.concreteChain) ancestors disclosed selected number
      (Prod.map id (Prod.map (PqxdhInitialParentPost.mapFront (RawCtxSelectedParentCalls.nativeKernel (nextChain parent))) id)
        result.1)) <$>
    (simulateQ (PqxdhInitialParentPrivateObserver.handler source writer (view (productionStream source.crypto) state.1.1.2.1)
      (fromOutput (PqxdhInitialBuilderContext.address context.original) parent)
      (view (productionStream source.crypto) state.1.1.2.1 (targetAddress (nextChain parent))) pre application initial selector aux
      (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain (nextChain parent))) (nextChain parent))
      (simulateQ PqxdhInitialParentObserverCompiler.compiler
        (PqxdhInitialOriginContext.stopped mark sender route decode context (material parent)))).run (nested (project state)) := by
  let decision : (Bool × PqxdhInitialOriginPostPath.Snapshot M P I D K S B) → Bool :=
    PqxdhInitialNativeParentEvent.nativeDecision (view (productionStream source.crypto) state.1.1.2.1)
    (fromOutput (PqxdhInitialBuilderContext.address context.original) parent) (nextChain parent)
    (view (productionStream source.crypto) state.1.1.2.1 (targetAddress (nextChain parent))) remaining
    ((earlier ++ [state.1.1.2.2.input]).map RawCtxFreshChainCut.concreteChain) ancestors disclosed selected number
  have evaluated := PqxdhInitialNativeParentRealization.source_compiled source writer pre application initial selector aux
    mark sender route decode context parent state matching separate
  have changed := congrArg (fun work => (fun result => decision result.1) <$> work) evaluated
  simp only [Functor.map_map] at changed
  rw [← changed]
  simp only [← bind_pure_comp]
  apply bind_congr_of_forall_mem_support
  intro result reached
  rw [PqxdhInitialNativeParentEvent.source_decision source writer
    (PqxdhInitialNativeAudit.external pre application initial selector aux)
    ((PqxdhInitialOriginContext.frame mark sender route decode context).2
      (PqxdhInitialParentBuilderContext.reply sender route decode context.original parent))
    state (PqxdhInitialBuilderContext.address context.original) parent missing matching separate root earlier walked result reached
    selected number remaining position (published result reached) ancestors disclosed]

end Frame

end BeaconcryptCore.Computational.PqxdhInitialNativeParentRandom

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentRandom.child_extends' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentRandom.child_extends

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentRandom.retained_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentRandom.retained_fresh

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentRandom.source_random' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentRandom.source_random

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentRandom.child_cursor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentRandom.child_cursor

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentRandom.retained_decision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentRandom.retained_decision

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentRandom.parent_random' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentRandom.parent_random

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentRandom.frame_random' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentRandom.frame_random

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentRandom.frame_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentRandom.frame_real

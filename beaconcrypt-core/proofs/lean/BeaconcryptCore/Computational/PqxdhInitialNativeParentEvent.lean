import BeaconcryptCore.Computational.PqxdhInitialNativeParentRealization
import BeaconcryptCore.Computational.PqxdhInitialPublishedEvent

/-!
The actual retained native continuation uses the published source cache to identify its byte-level freshness event. The source path and cache-extension facts are derived from the actual matched update and supported continuation; no final freshness-equivalence hypothesis is accepted. The initializer and all original ambient effects remain unchanged.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialNativeParentEvent
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids
open PqxdhInitialNativeLog PqxdhInitialNativeResponse PqxdhInitialNativeRetained
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedParentPrivatePatch RawCtxCursorLineage RawCtxSelectiveChainGame
variable {ι M P I D K X Response Shared A N C Result : Type} {extra : OracleSpec ι} {S B : Nat}

/-- The actual fresh parent insertion extends every previous binding. -/
theorem parent_extends (state : State A N C) (address : JointKdfAddress) (parent : FullOutput)
    (missing : state.1.1.2.1 address = none) :
    Extends state.1.1.2.1 (updated address parent state).1.1.2.1 := by
  intro request response present
  by_cases same : request = address
  · subst request
    rw [missing] at present
    cases present
  · exact (QueryCache.cacheQuery_of_ne (spec := JointKdfRO) state.1.1.2.1 parent same).trans present

/-- The source-matched fresh parent response extends the original root walk by precisely that parent's actual input. -/
theorem parent_walk (state : State A N C) (address : JointKdfAddress) (parent : FullOutput)
    (missing : state.1.1.2.1 address = none) (matching : matched state.1.1.2.2 address = true)
    (root : RootOutput) (earlier : List RootOutput)
    (walked : walk state.1.1.2.1 state.1.1.2.2.depth root = some (earlier, state.1.1.2.2.input)) :
    walk (updated address parent state).1.1.2.1 (state.1.1.2.2.depth + 1) root =
      some (earlier ++ [state.1.1.2.2.input], nextChain parent) := by
  have retained := walk_extends state.1.1.2.1 (updated address parent state).1.1.2.1
    (parent_extends state address parent missing) state.1.1.2.2.depth root _ walked
  have same : address = RawCtxFirstParentRisk.inputAddress state.1.1.2.2.input := by
    simpa only [matched, cursorAddress, RawCtxFirstParentRisk.inputAddress, decide_eq_true_eq] using matching
  rw [walk, retained]
  change ((state.1.1.2.1.cacheQuery address parent (RawCtxFirstParentRisk.inputAddress state.1.1.2.2.input)).bind
    fun output => some (earlier ++ [state.1.1.2.2.input], nextChain output)) = _
  rw [← same, QueryCache.cacheQuery_self]
  rfl

/-- The real post-parent source freshness is the literal finite observer checker plus the actual earlier root walk; final-cache agreement is derived from the supported saturated continuation. -/
theorem source_fresh (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared) (PqxdhInitialBeaconAmbient.Ambient A N C))
    (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B) Result)
    (state : State A N C) (address : JointKdfAddress) (parent : FullOutput)
    (missing : state.1.1.2.1 address = none) (matching : matched state.1.1.2.2 address = true)
    (separate : targetAddress (nextChain parent) ≠ address)
    (root : RootOutput) (earlier : List RootOutput)
    (walked : walk state.1.1.2.1 state.1.1.2.2.depth root = some (earlier, state.1.1.2.2.input))
    (result : Result × State A N C)
    (supported : result ∈ support ((simulateQ (handler source writer (state.1.1.2.2.depth + 1) external) client).run
      (updated address parent state)))
    (number : Std.U64) (remaining : Nat) (position : number.val = (state.1.1.2.2.depth + 1) + remaining + 1)
    (cached : RawCtxSourcePublishedPath.Cached root number result.2.1.1.2.1)
    (ancestors disclosed : List RatchetChain) (history : RawCtxProtocolReveals.History S B) :
    RawCtxLiveLineage.Fresh
      (RawCtxPublishedLineage.lineage (view (productionStream source.crypto) result.2.1.1.2.1)
        (RawCtxFreshChainCut.concreteChain root) (number.val - 1) ++ ancestors) disclosed history ↔
    RawCtxLiveLineage.Fresh
      ((PqxdhInitialParentStoppedHop.checkerTrace (view (productionStream source.crypto) state.1.1.2.1)
        (fromOutput address parent) (nextChain parent)
        (view (productionStream source.crypto) state.1.1.2.1 (targetAddress (nextChain parent))) (some remaining)).map
        (RawCtxSelectedChain.interpret (RawCtxFreshChainCut.concreteChain (nextChain parent))) ++
        ((earlier ++ [state.1.1.2.2.input]).map RawCtxFreshChainCut.concreteChain ++ ancestors)) disclosed history := by
  have past : state.1.1.2.2.depth + 1 ≤ (updated address parent state).1.1.2.2.depth := by
    simp only [updated, advance, matching, ite_true, le_refl]
  apply PqxdhInitialPublishedEvent.source_checked_fresh source
    (view (productionStream source.crypto) state.1.1.2.1) (fromOutput address parent) (nextChain parent)
    (view (productionStream source.crypto) state.1.1.2.1 (targetAddress (nextChain parent))) separate
    (updated address parent state).1.1.2.1 result.2.1.1.2.1
    (complete_replay source writer _ external client _ result supported).1 root number _ remaining position cached
    (earlier ++ [state.1.1.2.2.input]) (parent_walk state address parent missing matching root earlier walked)
  intro request response found
  rw [PqxdhInitialNativeParentRealization.consistent_patch,
    ← PqxdhInitialNativeParentContinuation.updated_view source address parent state]
  exact final_binding source writer _ external client (updated address parent state) past result supported request response found

noncomputable def nativeDecision (prior : Prior) (entry : Entry) (target : RootOutput) (output : FullOutput)
    (remaining : Nat) (earlier ancestors disclosed : List RatchetChain)
    (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (result : Bool × PqxdhInitialOriginPostPath.Snapshot M P I D K S B) : Bool :=
  @decide (PqxdhInitialPublishedEvent.Gate selected number result ∧ RawCtxLiveLineage.Fresh
    ((PqxdhInitialParentStoppedHop.checkerTrace prior entry target output (some remaining)).map
      (RawCtxSelectedChain.interpret (RawCtxFreshChainCut.concreteChain target)) ++ (earlier ++ ancestors))
    disclosed result.2.1.roles.2) (Classical.propDecidable _)

/-- On the original publication gate, the full source decision factors through its complete original result; private-table erasure is justified by actual cached publication and the supported source execution. -/
theorem source_decision (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (external : QueryImpl (External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N PqxdhCorrelatedExpand.RootOracle.QueryCache))
    (client : OracleComp (Spec extra RatchetChain I D K X Response Shared S B)
      (Bool × PqxdhInitialOriginPostPath.Snapshot M P I D K S B))
    (state : State A N PqxdhCorrelatedExpand.RootOracle.QueryCache) (address : JointKdfAddress) (parent : FullOutput)
    (missing : state.1.1.2.1 address = none) (matching : matched state.1.1.2.2 address = true)
    (separate : targetAddress (nextChain parent) ≠ address)
    (root : RootOutput) (earlier : List RootOutput)
    (walked : walk state.1.1.2.1 state.1.1.2.2.depth root = some (earlier, state.1.1.2.2.input))
    (result : (Bool × PqxdhInitialOriginPostPath.Snapshot M P I D K S B) ×
      State A N PqxdhCorrelatedExpand.RootOracle.QueryCache)
    (supported : result ∈ support ((simulateQ (handler source writer (state.1.1.2.2.depth + 1) external) client).run
      (updated address parent state)))
    (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (remaining : Nat)
    (position : number.val = (state.1.1.2.2.depth + 1) + remaining + 1)
    (published : PqxdhInitialPublishedEvent.Gate selected number result.1 →
      RawCtxSourcePublishedPath.Cached root number result.2.1.1.2.1)
    (ancestors disclosed : List RatchetChain) :
    PqxdhInitialPublishedEvent.sourceDecision source root selected number ancestors disclosed result =
      nativeDecision (view (productionStream source.crypto) state.1.1.2.1) (fromOutput address parent) (nextChain parent)
        (view (productionStream source.crypto) state.1.1.2.1 (targetAddress (nextChain parent))) remaining
        ((earlier ++ [state.1.1.2.2.input]).map RawCtxFreshChainCut.concreteChain) ancestors disclosed selected number result.1 := by
  apply Bool.eq_iff_iff.mpr
  simp only [PqxdhInitialPublishedEvent.source_decision, nativeDecision, decide_eq_true_eq,
    PqxdhInitialPublishedEvent.sourceEvent]
  exact and_congr_right (fun enabled => source_fresh source writer external client state address parent missing
    matching separate root earlier walked result supported number remaining position (published enabled)
    ancestors disclosed result.1.2.1.roles.2)

end BeaconcryptCore.Computational.PqxdhInitialNativeParentEvent

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentEvent.parent_extends' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentEvent.parent_extends

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentEvent.parent_walk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentEvent.parent_walk

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentEvent.source_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentEvent.source_fresh

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialNativeParentEvent.source_decision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialNativeParentEvent.source_decision

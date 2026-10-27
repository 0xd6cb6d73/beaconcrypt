import BeaconcryptCore.Computational.PqxdhNativeSharedContinuation
import BeaconcryptCore.Computational.PqxdhInitialPreparedResources
import BeaconcryptCore.Computational.PqxdhInitialPublishedEvent

/-! The actual parent sampler keeps completed and cached branches on their original same-ROM continuation. Only an actual missing private address returns a pending descriptor; the original publication/freshness event is preserved in every common branch. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhSharedParentCollect
open PqxdhNativeSharedPrefix PqxdhCorrelatedExpand
open CtxRomAuth AdaptiveCtxSharedHash PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhInitialBeaconAmbient
variable {ι I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (application : Response → LocalCallback A N RootOracle.QueryCache (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N RootOracle.QueryCache PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))

variable {M P : Type}
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (root : RootOutput) (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (ancestors disclosed : List RatchetChain)

noncomputable def decision
    (result : PqxdhInitialNativeCarried.Final M P I D K Bool Bool S B × Local A N RootOracle.QueryCache) : Bool :=
  PqxdhInitialPublishedEvent.sourceDecision source root selected number ancestors disclosed (result.1, (attach result.2 ∅).1)

/-- The literal final publication and value-freshness predicate does not inspect the external commitment cache. -/
theorem decision_cache
    (result : PqxdhInitialNativeCarried.Final M P I D K Bool Bool S B × Local A N RootOracle.QueryCache) (cache : CtxRO.QueryCache) :
    decision source root selected number ancestors disclosed result =
      PqxdhInitialPublishedEvent.sourceDecision source root selected number ancestors disclosed (result.1, (attach result.2 cache).1) := rfl

abbrev Pending (extra : OracleSpec ι) (M P I D K A N C : Type) (S B : Nat) :=
  PqxdhInitialNativeCarried.Context extra M P I D K Bool Bool S B × Local A N C

def restore (input : Bool ⊕ Pending extra M P I D K A N RootOracle.QueryCache S B) (cache : CtxRO.QueryCache) :
    Bool ⊕ PqxdhInitialPreparedParent.Pending extra M P I D K Bool Bool A N RootOracle.QueryCache S B :=
  match input with
  | .inl decision => .inl decision
  | .inr input => .inr (input.1, attach input.2 cache)

noncomputable def collect (depth : Nat)
    (cut : PqxdhNativeSharedContinuation.Carried extra M P I D K Bool Bool A N RootOracle.QueryCache S B) :
    OracleComp HashSpec (Bool ⊕ Pending extra M P I D K A N RootOracle.QueryCache S B) := by
  classical
  exact match cut with
  | .complete result state => pure (.inl (decision source root selected number ancestors disclosed (result, state)))
  | .pending context state =>
    if state.store.1 (PqxdhInitialBuilderContext.address context.original) = none then pure (.inr (context, state))
    else do
      let result ← PqxdhNativeSharedContinuation.finish source writer (depth + 1) pre application initial selector aux mark sender route decode cut
      pure (.inl (decision source root selected number ancestors disclosed result))

/-- The same missing/hit test and full cached continuation produce the literal original prepared sample, including its complete source Gate/Fresh decision. -/
theorem collect_source (depth : Nat)
    (cut : PqxdhNativeSharedContinuation.Carried extra M P I D K Bool Bool A N RootOracle.QueryCache S B) (cache : CtxRO.QueryCache) :
    (fun result => restore result.1 result.2) <$>
      (simulateQ hashImpl (collect source writer pre application initial selector aux mark sender route decode
        root selected number ancestors disclosed depth cut)).run cache =
    PqxdhInitialPreparedParent.collect source writer (fun request => localLift (pre request))
      (fun reply => localLift (application reply)) (fun secrets => localLift (initial secrets))
      (fun request => localLift (selector request)) (fun request => localLift (aux request)) mark sender route decode
      (fun result => pure (PqxdhInitialPublishedEvent.sourceDecision source root selected number ancestors disclosed result)) depth
      (RawCtxSharedPrefixScan.restore attach (cut, cache)) := by
  classical
  cases cut with
  | complete result state => rfl
  | pending context state =>
    simp only [collect, RawCtxSharedPrefixScan.restore, PqxdhInitialPreparedParent.collect]
    change (fun result => restore result.1 result.2) <$> (simulateQ hashImpl
      (if state.store.1 (PqxdhInitialBuilderContext.address context.original) = none then _ else _)).run cache =
      if state.store.1 (PqxdhInitialBuilderContext.address context.original) = none then _ else _
    split
    · rfl
    · have original := congrArg (fun work =>
        (fun result => (Sum.inl (PqxdhInitialPublishedEvent.sourceDecision source root selected number ancestors disclosed result) :
          Bool ⊕ PqxdhInitialPreparedParent.Pending extra M P I D K Bool Bool A N RootOracle.QueryCache S B)) <$> work)
        (PqxdhNativeSharedContinuation.finish_source source writer (depth + 1) pre application initial selector aux
          mark sender route decode (.pending context state) cache)
      simpa only [simulateQ_bind, StateT.run_bind, map_bind, simulateQ_pure, StateT.run_pure,
        map_pure, bind_pure_comp, simulateQ_map, StateT.run_map, Functor.map_map, restore, ← decision_cache,
        PqxdhInitialPreparedParent.finish, RawCtxSharedPrefixScan.restore] using original

end BeaconcryptCore.Computational.PqxdhSharedParentCollect


/-- info: 'BeaconcryptCore.Computational.PqxdhSharedParentCollect.decision_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSharedParentCollect.decision_cache

/-- info: 'BeaconcryptCore.Computational.PqxdhSharedParentCollect.collect_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSharedParentCollect.collect_source

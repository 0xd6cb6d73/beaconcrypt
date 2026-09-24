import BeaconcryptCore.Computational.RawCtxSharedPrefixBounds
import BeaconcryptCore.Computational.RawCtxSharedPendingBounds

/-!
The actual audited first-builder/adaptive-post prefix has at most7+67*qPost source callbacks. Every callback pays its source-local randomness or original private76 draw; commitment lookups are counted separately and still count on cache hits. No completed observer or security event is assumed to have a cost bound.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhNativeSharedPrefixBounds
open PqxdhJointKdfGame PqxdhNativeSharedPrefix AdaptiveCtxSharedHash
variable {ι M P I D K X Response Shared Result Origin A N C : Type} {extra : OracleSpec ι} {S B : Nat}

/-- Every compiled live source callback pays at most one hash or76 uniform requests. The actual reveals and failed branches retain their lower costs. -/
theorem live_bound (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (hash : Bool) (query : (RawCtxPendingSelectiveFamily.Spec S B).Domain) (state : Local A N C) :
    ((live source writer stage query).run state).IsQueryBoundP (HashClass hash) (if hash then 1 else 76) := by
  change ((fun result => (result.1, { state with
      shared := result.2.1
      store := result.2.2
      inputs := RawCtxSelectiveFamilyLog.inputs query state.inputs
      audit := state.audit ++ PqxdhInitialNativeAudit.liveInputs query })) <$>
      (RawCtxSelectiveSharedRom.pending source writer stage query).run (state.shared, state.store)).IsQueryBoundP (HashClass hash) (if hash then 1 else 76)
  rw [isQueryBoundP_map_iff]
  apply (RawCtxSharedPendingBounds.live source writer stage hash query (state.shared, state.store)).mono
  rcases query with ((request | opening) | ((request | sealing) | (coin | (bytes | view)))) | read
  all_goals cases hash <;> simp [RawCtxSharedPendingBounds.liveCost, RawCtxSharedPendingBounds.publicCost]

/-- The source-local callback forwards all its original coins and no commitment hash. -/
theorem local_bound {Value : Type} (hash : Bool) (work : LocalCallback A N C Value)
    (q : Nat) (bounded : ∀ state, (work.run state).IsTotalQueryBound q) (state : Local A N C) :
    ((localCall work).run state).IsQueryBoundP (HashClass hash) (if hash then 0 else q) := by
  cases hash
  · exact (PqxdhPreparedPrefixCallbacks.local_bills work state q (bounded _)).2
  · exact (PqxdhPreparedPrefixCallbacks.local_bills work state q (bounded _)).1

/-- The retained initializer pays its original source computation; appending its full audit adds no oracle query. -/
theorem initial_bound (hash : Bool) (work : LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (q : Nat) (bounded : ∀ state, (work.run state).IsTotalQueryBound q) (state : Local A N C) :
    ((initialCall work).run state).IsQueryBoundP (HashClass hash) (if hash then 0 else q) := by
  simp only [initialCall, StateT.run, isQueryBoundP_map_iff]
  cases hash
  · exact RawCtxSelectiveSharedRom.coins_bound _ q (bounded _)
  · exact RawCtxSelectiveSharedRom.coins_no_hash _

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (qPre qApplication qInitial qSelector qAux : Nat)
    (preBound : ∀ query state, ((pre query).run state).IsTotalQueryBound qPre)
    (applicationBound : ∀ query state, ((application query).run state).IsTotalQueryBound qApplication)
    (initialBound : ∀ query state, ((initial query).run state).IsTotalQueryBound qInitial)
    (selectorBound : ∀ query state, ((selector query).run state).IsTotalQueryBound qSelector)
    (auxBound : ∀ query state, ((aux query).run state).IsTotalQueryBound qAux)

include preBound applicationBound initialBound selectorBound auxBound in
/-- The entire concrete audited callback pays its primitive cost and the explicit source-local allowance. No ambient work is omitted. -/
theorem step_bound (hash : Bool) (query : (PqxdhInitialNativeAudit.Spec extra RatchetChain I D K X Response Shared S B).Domain)
    (state : Local A N C) :
    ((compiler source writer stage pre application initial selector aux query).run state).IsQueryBoundP
      (HashClass hash) (if hash then 1 else 76 + qPre + qApplication + qInitial + qSelector + qAux) := by
  rcases query with query | (query | (reply | (secrets | (query | query))))
  · exact (live_bound source writer stage hash query state).mono (by cases hash <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega)
  · exact (local_bound hash (pre query) qPre (preBound query) state).mono (by cases hash <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega)
  · exact (local_bound hash (application reply) qApplication (applicationBound reply) state).mono (by cases hash <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega)
  · exact (initial_bound hash (initial secrets) qInitial (initialBound secrets) state).mono (by cases hash <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega)
  · exact (local_bound hash (selector query) qSelector (selectorBound query) state).mono (by cases hash <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega)
  · exact (local_bound hash (aux query) qAux (auxBound query) state).mono (by cases hash <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega)

variable (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (execution : PqxdhInitialNativeAuditCarried.Execution extra M P I D K Result Origin S B)

/-- The carried code is the original first builder and adaptive post schedule, with exactly the proved7+67*qPost callback cap. -/
theorem code_total (qPost : Nat) (bounded : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost) :
    (PqxdhInitialNativeCarried.code (X := X) (Response := Response) source mark sender route decode execution).IsTotalQueryBound (7 + qPost * 67) := by
  apply (RawCtxSharedPrefixBounds.annotation_total _ _).mp
  simpa only [PqxdhInitialNativeCarried.code, PqxdhInitialOriginForwardBuilder.program_erase] using
    PqxdhInitialOriginPost.sequence_total source execution.initial mark execution.origin sender route decode
      execution.index execution.metadata execution.ready execution.outside qPost bounded (execution.before, execution.trace)

include preBound applicationBound initialBound selectorBound auxBound in
/-- The complete actual carried prefix has the explicit H/U ledger, derived from its original source callback and post bounds. -/
theorem carried_bound (depth qPost : Nat) (bounded : ∀ reply, (execution.outside reply).IsTotalQueryBound qPost)
    (hash : Bool) (state : Local A N C) :
    (carried source writer stage pre application initial selector aux mark sender route decode execution depth state).IsQueryBoundP
      (HashClass hash) ((7 + qPost * 67) * (if hash then 1 else 76 + qPre + qApplication + qInitial + qSelector + qAux)) := by
  exact RawCtxSharedPrefixBounds.scan_bound _ _ _ _ (HashClass hash) _
    (step_bound source writer stage pre application initial selector aux qPre qApplication qInitial qSelector qAux
      preBound applicationBound initialBound selectorBound auxBound hash)
    _ _ _ (code_total source mark sender route decode execution qPost bounded) state

end BeaconcryptCore.Computational.PqxdhNativeSharedPrefixBounds


/-- info: 'BeaconcryptCore.Computational.PqxdhNativeSharedPrefixBounds.live_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhNativeSharedPrefixBounds.live_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhNativeSharedPrefixBounds.local_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhNativeSharedPrefixBounds.local_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhNativeSharedPrefixBounds.initial_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhNativeSharedPrefixBounds.initial_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhNativeSharedPrefixBounds.step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhNativeSharedPrefixBounds.step_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhNativeSharedPrefixBounds.code_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhNativeSharedPrefixBounds.code_total

/-- info: 'BeaconcryptCore.Computational.PqxdhNativeSharedPrefixBounds.carried_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhNativeSharedPrefixBounds.carried_bound

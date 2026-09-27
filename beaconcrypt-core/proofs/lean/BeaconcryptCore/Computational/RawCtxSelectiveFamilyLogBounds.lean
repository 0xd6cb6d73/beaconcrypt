import BeaconcryptCore.Computational.RawCtxSelectiveFamilyLog
import BeaconcryptCore.Computational.RawCtxGenericFamilyBudgets

/-!
The original bounded LIVE family supplies the exact enriched private-call cap S+51R. Every actual private receive/send callback is counted, including repeated cache hits and callbacks in rejected record attempts. The chronological log grows only after those executed callbacks; both full executions and state-dependent prefixes retain the actual initial input list and obey the source cap without enumerating a functional cache or transferring costs across distribution equality.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds
open RawCtxPendingOwnerQueries RawCtxServerServiceBounds RawCtxSelectiveFamilyLog
open PqxdhJointKdf PqxdhJointKdfGame

/-- The actual enriched receive program counts every pending KDF callback under every typed reply. -/
theorem receive_private {Chain : Type} (entry : Kernel Chain) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    (calls.receive entry target context).IsQueryBoundP (fun query => RawCtxPendingMixedPrefix.ownerSelected query = true) 51 := by
  apply RawCtxSourceOpen.simulate_bound receiveForward (fun query => query.isLeft = true) _ _ 51
    (RawCtxPendingReceiveQueries.receive_bound entry target context)
  intro query
  cases query <;> exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [RawCtxPendingMixedPrefix.ownerSelected])

private theorem send_program_private {Chain : Type}
    (start : RawCtxChainSend.Start Chain Chain RatchetMaterial RawCtxSourceSend.SealContext) :
    (sendProgram start).IsQueryBoundP (fun query => query.isLeft = true) 1 := by
  cases start with
  | exhausted => trivial
  | requested pending =>
    simp only [sendProgram]
    change IsQueryBoundP (((SendSpec Chain).query (.inl pending) : OracleComp (SendSpec Chain) _) >>=
      fun reply => (fun sealed => ((RawCtxChainSend.ready pending reply).advanced, sealed)) <$>
        ((SendSpec Chain).query (.inr (RawCtxChainSend.ready pending reply)))) (fun query => query.isLeft = true) 1
    rw [isQueryBoundP_query_bind_iff]
    constructor
    · simp
    · intro reply
      change OracleComp.IsQueryBoundP
        ((fun sealed => ((RawCtxChainSend.ready pending reply).advanced, sealed)) <$>
          ((SendSpec Chain).query (.inr (RawCtxChainSend.ready pending reply)) : OracleComp (SendSpec Chain) _))
        (fun query => query.isLeft = true) 0
      rw [isQueryBoundP_map_iff]
      exact (isQueryBoundP_query_iff (spec := SendSpec Chain) (fun query => query.isLeft = true) (.inr (RawCtxChainSend.ready pending reply)) 0).mpr (by simp)

/-- Exhausted sends reject, and every original requested send has exactly its one enriched private KDF callback before sealing. -/
theorem send_private {Chain : Type} (entry : Kernel Chain) (context : RawCtxSourceSend.SealContext) :
    (calls.send entry context).IsQueryBoundP (fun query => RawCtxPendingMixedPrefix.ownerSelected query = true) 1 := by
  apply RawCtxSourceOpen.simulate_bound sendForward (fun query => query.isLeft = true) _ _ 1
    (send_program_private (RawCtxChainSend.normalBegin entry context))
  intro query
  cases query <;> exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [RawCtxPendingMixedPrefix.ownerSelected])

def privateWeight : Kind → Nat
  | .send => 1
  | .raw => 51
  | _ => 0

def privateQuery {S B : Nat} (query : (RawCtxPendingSelectiveFamily.Spec S B).Domain) : Prop :=
  RawCtxSelectedFamilyContext.queryAddress query ≠ none

instance {S B : Nat} : DecidablePred (privateQuery (S := S) (B := B)) :=
  fun query => inferInstanceAs (Decidable (RawCtxSelectedFamilyContext.queryAddress query ≠ none))

/-- All original role-family gates and indexed updates retain the exact private KDF request cost of their source operation. -/
theorem family_private {M P I D K : Type} {S B : Nat}
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (state : RawCtxPendingFamilyTails.State RatchetChain M P I D K S B) :
    ((RawCtxGenericFamilyFrontend.impl calls publicForward sender route decode query).run state).IsQueryBoundP
      (fun query => RawCtxPendingMixedPrefix.ownerSelected query = true) (privateWeight (RawCtxProtocolBudgets.sourceKind query)) := by
  apply RawCtxGenericFamilyBudgets.family_step calls publicForward
    (fun query => RawCtxPendingMixedPrefix.ownerSelected query = true) privateWeight
    receive_private send_private ?_ sender route decode query state
  intro query
  apply (isQueryBoundP_query_iff _ _ _).mpr
  rcases query with coin | (hash | hkdf)
  all_goals simp [RawCtxPendingMixedPrefix.ownerSelected, privateWeight, sourceKind]

/-- Exact pending LIVE forwarding preserves each private role callback; public services and reads add no private KDF input. -/
theorem source_step {M P I D K : Type} {S B : Nat}
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (state : RawCtxPendingFamilyLiveQueries.State RatchetChain M P I D K S B) :
    ((RawCtxPendingFamilyLiveQueries.compiler sender route decode query).run state).IsQueryBoundP privateQuery
      (RawCtxRevealBudgets.weight privateWeight 0 query) := by
  cases query with
  | inl request =>
    simp only [RawCtxPendingFamilyLiveQueries.compiler, StateT.run, bind_pure_comp,
      isQueryBoundP_map_iff, RawCtxRevealBudgets.weight]
    apply RawCtxSourceOpen.simulate_bound RawCtxPendingFamilyLiveQueries.primitiveForward
      (fun query => RawCtxPendingMixedPrefix.ownerSelected query = true) privateQuery _ _
      (family_private sender route decode request state.1)
    intro query
    apply (isQueryBoundP_query_iff _ _ _).mpr
    rcases query with (pending | opening) | ((pending | sealing) | publicQuery)
    all_goals simp [privateQuery, RawCtxSelectedFamilyContext.queryAddress, RawCtxSelectedFamilyContext.primitiveAddress,
      RawCtxPendingMixedPrefix.ownerSelected]
  | inr request =>
    simp only [RawCtxPendingFamilyLiveQueries.compiler, StateT.run, bind_pure_comp,
      isQueryBoundP_map_iff, RawCtxRevealBudgets.weight]
    exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [privateQuery, RawCtxSelectedFamilyContext.queryAddress])

/-- Every enriched private callback in the original all-reply LIVE schedule is charged by S+51R, including cache hits. -/
theorem program_private {M P I D K Result : Type} {S B : Nat}
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : RawCtxPendingFamilyLiveQueries.State RatchetChain M P I D K S B) :
    (RawCtxPendingFamilyLiveTails.program sender route decode client state).IsQueryBoundP privateQuery
      (budget.1 .send + 51 * budget.1 .raw) := by
  have cap := RawCtxRevealBudgets.weighted_bound (RawCtxPendingFamilyLiveQueries.compiler sender route decode)
    privateQuery privateWeight 0 client budget bounded (source_step sender route decode) state
  have enumeration : (Finset.univ : Finset Kind) = {.send, .raw, .coin, .hash, .hkdf} := by decide
  simpa [RawCtxRevealBudgets.bill, RawCtxServerServiceBounds.bill, enumeration, privateWeight, RawCtxPendingFamilyLiveTails.program] using cap

/-- The actual original native family uses the same enriched S+51R private-input count, with every supplied initial correlation retained. -/
theorem source_private {M P I D K Result : Type} {S B : Nat}
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : RawCtxProtocolReveals.State M P I D K S B) :
    (RawCtxPendingSelectiveFamily.program sender route decode client state).IsQueryBoundP privateQuery
      (budget.1 .send + 51 * budget.1 .raw) :=
  program_private sender route decode client budget bounded _

/-- A callback appends precisely one actual private address, and every other callback retains the same input list. -/
theorem inputs_length {S B : Nat} (query : (RawCtxPendingSelectiveFamily.Spec S B).Domain) (past : List JointKdfAddress) :
    (inputs query past).length = past.length + (if privateQuery query then 1 else 0) := by
  cases found : RawCtxSelectedFamilyContext.queryAddress query <;> simp [inputs, privateQuery, found]

/-- A complete actual logged execution pays every executed private callback after it returns, retaining the original initial list. -/
theorem program_length {Auxiliary Result : Type} {S B : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (client : OracleComp (RawCtxPendingSelectiveFamily.Spec S B) Result)
    (budget : Nat) (bounded : client.IsQueryBoundP privateQuery budget)
    (state : LoggedState Auxiliary) (result : Result × LoggedState Auxiliary)
    (supported : result ∈ support ((simulateQ (RawCtxSelectiveFamilyLog.handler source writer stage) client).run state)) :
    result.2.2.length ≤ state.2.length + budget := by
  induction client using OracleComp.inductionOn generalizing budget state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact Nat.le_add_right _ _
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
    simp only [RawCtxSelectiveFamilyLog.handler, StateT.run, bind_assoc, pure_bind, mem_support_bind_iff] at supported
    obtain ⟨reply, _, tail⟩ := supported
    have rest := ih reply.1 _ (bounded.2 reply.1) (reply.2, inputs query state.2) result tail
    rw [inputs_length] at rest
    by_cases counted : privateQuery query
    · have positive : 0 < budget := bounded.1.resolve_left (not_not_intro counted)
      simp only [counted, if_true] at rest
      omega
    · simpa only [counted, if_false, Nat.add_zero] using rest

/-- Every actual state-dependent stopped prefix pays only its executed private callbacks; the saved pending query has not yet been appended. -/
theorem scan_length {Auxiliary Result : Type} {S B : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selected : (RawCtxPendingSelectiveFamily.Spec S B).Domain → LoggedState Auxiliary → Bool)
    (client : OracleComp (RawCtxPendingSelectiveFamily.Spec S B) Result)
    (budget : Nat) (bounded : client.IsQueryBoundP privateQuery budget)
    (state : LoggedState Auxiliary)
    (result : RawCtxPendingMixedPrefix.Prefix (RawCtxPendingSelectiveFamily.Spec S B) Result (LoggedState Auxiliary))
    (supported : result ∈ support (RawCtxStatefulPendingPrefix.scan selected
      (RawCtxSelectiveFamilyLog.handler source writer stage) client state)) :
    result.2.2.length ≤ state.2.length + budget := by
  induction client using OracleComp.inductionOn generalizing budget state result with
  | pure value =>
    simp only [RawCtxStatefulPendingPrefix.scan_pure, mem_support_pure_iff] at supported
    subst result
    exact Nat.le_add_right _ _
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    cases chosen : selected query state with
    | true =>
      rw [RawCtxStatefulPendingPrefix.scan_cut selected (RawCtxSelectiveFamilyLog.handler source writer stage)
        query next state chosen, mem_support_pure_iff] at supported
      subst result
      exact Nat.le_add_right _ _
    | false =>
      rw [RawCtxStatefulPendingPrefix.scan_other selected (RawCtxSelectiveFamilyLog.handler source writer stage)
        query next state chosen] at supported
      simp only [RawCtxSelectiveFamilyLog.handler, StateT.run, bind_assoc, pure_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, _, tail⟩ := supported
      have rest := ih reply.1 _ (bounded.2 reply.1) (reply.2, inputs query state.2) result tail
      rw [inputs_length] at rest
      by_cases counted : privateQuery query
      · have positive : 0 < budget := bounded.1.resolve_left (not_not_intro counted)
        simp only [counted, if_true] at rest
        omega
      · simpa only [counted, if_false, Nat.add_zero] using rest

/-- The actual full native family execution retains its initial root-input list and appends at most S+51R executed private requests. -/
theorem source_length {M P I D K Auxiliary Result : Type} {S B : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : RawCtxProtocolReveals.State M P I D K S B)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) (store : RawCtxSelectiveChainGame.Store)
    (past : List JointKdfAddress)
    (result : (Result × RawCtxProtocolReveals.State M P I D K S B) × LoggedState Auxiliary)
    (supported : result ∈ support (RawCtxSelectiveFamilyLog.family source writer stage sender route decode
      client state primitive store past)) :
    result.2.2.length ≤ past.length + (budget.1 .send + 51 * budget.1 .raw) := by
  simp only [RawCtxSelectiveFamilyLog.family, support_map, Set.mem_image] at supported
  obtain ⟨before, supported, rfl⟩ := supported
  exact program_length source writer stage _ _ (source_private sender route decode client budget bounded state)
    ((primitive, store), past) before supported

/-- The actual native family's state-dependent source prefix retains the same explicit initial list and the S+51R cap, without charging its unexecuted saved query. -/
theorem source_scan_length {M P I D K Auxiliary Result : Type} {S B : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (selected : (RawCtxPendingSelectiveFamily.Spec S B).Domain → LoggedState Auxiliary → Bool)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : RawCtxProtocolReveals.State M P I D K S B)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary) (store : RawCtxSelectiveChainGame.Store)
    (past : List JointKdfAddress)
    (result : RawCtxPendingMixedPrefix.Prefix (RawCtxPendingSelectiveFamily.Spec S B)
      (Result × RawCtxPendingFamilyLiveQueries.State RatchetChain M P I D K S B) (LoggedState Auxiliary))
    (supported : result ∈ support (RawCtxStatefulPendingPrefix.scan selected
      (RawCtxSelectiveFamilyLog.handler source writer stage)
      (RawCtxPendingSelectiveFamily.program sender route decode client state) ((primitive, store), past))) :
    result.2.2.length ≤ past.length + (budget.1 .send + 51 * budget.1 .raw) := by
  exact scan_length source writer stage selected _ _ (source_private sender route decode client budget bounded state)
    ((primitive, store), past) result supported

end BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds.receive_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds.receive_private

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds.send_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds.send_private

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds.family_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds.family_private

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds.source_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds.source_step

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds.program_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds.program_private

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds.source_private' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds.source_private

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds.inputs_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds.inputs_length

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds.program_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds.program_length

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds.scan_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds.scan_length

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds.source_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds.source_length

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds.source_scan_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectiveFamilyLogBounds.source_scan_length

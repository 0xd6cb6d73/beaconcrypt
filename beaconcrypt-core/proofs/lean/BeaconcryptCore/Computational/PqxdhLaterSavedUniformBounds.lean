import BeaconcryptCore.Computational.PqxdhLaterSavedPostBounds

/-! Complete callback costs for the saved continuation and adaptive Post. Every original source-local random call remains charged, including work before optional failure or component refusal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterSavedUniformBounds

/-- A uniform finite service allowance composes through the full stateful source program on every oracle-reply path. -/
theorem state_cost {ι κ σ R : Type} {sourceSpec : OracleSpec ι} {targetSpec : OracleSpec κ}
    (handler : QueryImpl sourceSpec (StateT σ (OracleComp targetSpec)))
    (predicate : targetSpec.Domain → Prop) [DecidablePred predicate] (cost : Nat)
    (step : ∀ query before, ((handler query).run before).IsQueryBoundP predicate cost)
    (work : OracleComp sourceSpec R) (q : Nat) (bounded : work.IsTotalQueryBound q) (before : σ) :
    ((simulateQ handler work).run before).IsQueryBoundP predicate (q * cost) := by
  induction work using OracleComp.inductionOn generalizing q before with
  | pure value => trivial
  | query_bind query continuation ih =>
    rw [isTotalQueryBound_query_bind_iff] at bounded
    obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt bounded.1)
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, Nat.succ_mul, Nat.add_comm]
    exact isQueryBoundP_bind (step query before) (fun reply _ => ih reply.1 remaining (by simpa using bounded.2 reply.1) reply.2)


open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedMessageDriver
open PqxdhSelectedFirstRecord PqxdhFirstRecordConfidentiality
variable {ι I D K X Response Shared A N C M P Result : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (monitor : Fin B)
variable (predicate : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Prop) [DecidablePred predicate]
    (cost : Nat) (positive : 1 ≤ cost)
    (externalBound : ∀ query localState,
      ((PqxdhSelectedCallbackCompiler.lower pre application initial selector aux (.inl query)).run localState).IsQueryBoundP predicate cost)

include positive externalBound

/-- The literal owner service retains every source callback charge and the complete attempted first opening. -/
theorem owner_step (query : (PqxdhSelectedInitialOwnerCompiler.Spec extra I D K X Response Shared).Domain)
    (before : Local A N C) :
    ((PqxdhSelectedInitialOwnerCompiler.lower pre application initial selector aux prior parent target nonce next read query).run before).IsQueryBoundP predicate cost := by
  cases query with
  | inl query => exact externalBound query before
  | inr request =>
    simp only [PqxdhSelectedInitialOwnerCompiler.lower, StateT.run, isQueryBoundP_map_iff]
    exact (PqxdhSelectedBeaconCompiler.finish_queries prior parent target nonce next read request.control request.before
      request.candidate request.kernel request.application).isQueryBoundP.mono positive

/-- A complete attempted owner finish includes at most sixteen literal service calls, each paid at the concrete callback allowance. -/
theorem owner_cost (raw : Pqxdh.Bytes) (owner : PqxdhSelectedInitialOwnerCompiler.Beacon I D K) (before : Local A N C) :
    ((simulateQ (PqxdhSelectedInitialOwnerCompiler.lower pre application initial selector aux prior parent target nonce next read)
      (PqxdhSelectedInitialOwnerCompiler.owner raw owner)).run before).IsQueryBoundP predicate (16 * cost) := by
  apply state_cost _ predicate cost
    (owner_step pre application initial selector aux prior parent target nonce next read predicate cost positive externalBound)
    _ 16 (PqxdhSelectedInitialOwnerCompiler.owner_queries raw owner)

/-- Each original Post request pays its full record/public operation, selector work or complete attempted owner finish. -/
theorem post_step (query : (PqxdhInitialGenericPost.Spec extra S B).Domain)
    (before : PqxdhSelectedPostCompiler.State M P I D K A N C S B) :
    (((PqxdhSelectedPostCompiler.impl pre application initial selector aux fixed writer prior parent target nonce next sender route read query).run).run before).IsQueryBoundP predicate (16 * cost) := by
  rcases query with (request | request) | request
  · simp only [PqxdhSelectedPostCompiler.impl, OptionT.run_mk, StateT.run, isQueryBoundP_map_iff]
    exact (RawCtxSelectedFamilyLiveCompiler.step_queries fixed writer prior parent target nonce next sender route read request before.1.roles).isQueryBoundP.mono
      (by cases request <;> simp only [RawCtxRevealBudgets.weight] <;> omega)
  · simp only [PqxdhSelectedPostCompiler.impl, OptionT.run_mk, StateT.run, isQueryBoundP_map_iff]
    exact (externalBound _ before.2).mono (by omega)
  · cases request with
    | finish index raw =>
      simpa only [PqxdhSelectedPostCompiler.impl, OptionT.run_mk, StateT.run, isQueryBoundP_map_iff] using
        owner_cost pre application initial selector aux prior parent target nonce next read predicate cost positive externalBound
          raw (before.1.roles.1.2 index) before.2

/-- Instrumentation preserves the exact oracle syntax; all adaptive Post callbacks remain paid, including the callback that refuses and stops the continuation. -/
theorem post_cost (work : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (qPost : Nat) (bounded : work.IsTotalQueryBound qPost) (before : InsState M P I D K A N C S B) :
    (((simulateQ (insImpl pre application initial selector aux fixed writer prior parent target nonce next sender route read mark monitor)
      work).run).run before).IsQueryBoundP predicate (qPost * (16 * cost)) := by
  induction work using OracleComp.inductionOn generalizing qPost before with
  | pure value => trivial
  | query_bind query continuation ih =>
    rw [isTotalQueryBound_query_bind_iff] at bounded
    obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt bounded.1)
    have step := post_step pre application initial selector aux fixed writer prior parent target nonce next sender route read
      predicate cost positive externalBound query before.1
    rw [← insImpl_erase pre application initial selector aux fixed writer prior parent target nonce next sender route read mark monitor query before,
      isQueryBoundP_map_iff] at step
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
    rw [Nat.succ_mul, Nat.add_comm]
    apply isQueryBoundP_bind (m := remaining * (16 * cost)) step
    rintro ⟨none | answer, after⟩ _
    · trivial
    · exact ih answer remaining (by simpa using bounded.2 answer) after

omit positive in
/-- Both original publication callbacks are charged, including an attempted serialization returning no frame. -/
theorem publication_cost (saved : PqxdhInitialBuilderContext.Builder extra M P I D K Result S B)
    (material : PqxdhOrderedChainHybrids.Material) (sealed : Option RawCtxSourceSend.Encrypted)
    (before : Local A N C) :
    ((PqxdhLaterSavedPostCompiler.publication pre application initial selector aux target sender saved material sealed).run before).IsQueryBoundP predicate (cost + cost) := by
  simp only [PqxdhLaterSavedPostCompiler.publication, PqxdhInitialBuilderContext.afterSend, StateT.run_bind]
  apply isQueryBoundP_bind (externalBound _ before)
  intro erased _
  cases sealed with
  | none => trivial
  | some encrypted =>
    simp only [StateT.run_bind]
    simpa only [Nat.add_zero] using isQueryBoundP_bind (m := 0) (externalBound _ erased.2) (fun serialized _ => by cases serialized.1 <;> trivial)

omit positive in
/-- Saved record and finish operations retain their one-call allowance; saved builders additionally retain both source-local publication callbacks. -/
theorem prepare_cost (qPost : Nat) (context : PqxdhInitialOriginContext.Context extra M P I D K Result Bool S B)
    (material : PqxdhOrderedChainHybrids.Material) (fits : PqxdhInitialOriginCertificates.Fits qPost context)
    (before : Local A N C) :
    (PqxdhLaterSavedPostCompiler.prepare pre application initial selector aux fixed writer prior target nonce next sender read
      qPost context material fits before).IsQueryBoundP predicate (1 + (cost + cost)) := by
  rcases context with ⟨original, trace, origin⟩
  cases original with
  | inl original =>
    cases original with
    | record request roles outside inner =>
      unfold PqxdhLaterSavedPostCompiler.prepare
      exact isQueryBoundP_bind
        (RawCtxSelectedPendingRoleCompiler.live_queries fixed writer prior target nonce next read inner material fits.2).isQueryBoundP
        (fun _ _ => by trivial)
    | finish index roles control candidate outside inner =>
      unfold PqxdhLaterSavedPostCompiler.prepare
      exact isQueryBoundP_bind
        (RawCtxSelectedPendingOwnerCompiler.owner_queries fixed writer prior target nonce next read inner material fits.2).isQueryBoundP
        (fun _ _ => by trivial)
  | inr saved =>
    unfold PqxdhLaterSavedPostCompiler.prepare
    apply isQueryBoundP_bind (RawCtxSelectedPendingSendCompiler.sealing_queries fixed.crypto writer _).isQueryBoundP
    intro sealed _
    simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
      publication_cost pre application initial selector aux target sender predicate cost externalBound saved material sealed before

/-- The actual saved operation and complete original adaptive Post retain every callback cost, including both optional publication callbacks. -/
theorem complete_cost (qPost : Nat) (context : PqxdhInitialOriginContext.Context extra M P I D K Result Bool S B)
    (material : PqxdhOrderedChainHybrids.Material) (fits : PqxdhInitialOriginCertificates.Fits qPost context)
    (before : Local A N C) :
    (PqxdhLaterSavedPostCompiler.complete pre application initial selector aux fixed writer prior target nonce next mark sender route read monitor
      qPost context material fits before).IsQueryBoundP predicate (1 + (cost + cost) + qPost * (16 * cost)) := by
  unfold PqxdhLaterSavedPostCompiler.complete
  apply isQueryBoundP_bind
    (prepare_cost pre application initial selector aux fixed writer prior target nonce next sender read predicate cost externalBound
      qPost context material fits before)
  intro prepared supported
  exact post_cost pre application initial selector aux fixed writer prior
    (some (Entry.mk (PqxdhInitialBuilderContext.address context.original) material)) target nonce next mark sender route read monitor
    predicate cost positive externalBound prepared.1 qPost
    (PqxdhLaterSavedPostBounds.prepare_post pre application initial selector aux fixed writer prior target nonce next sender read
      qPost context material fits before prepared supported) prepared.2

end BeaconcryptCore.Computational.PqxdhLaterSavedUniformBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedUniformBounds.state_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedUniformBounds.state_cost
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedUniformBounds.owner_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedUniformBounds.owner_step
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedUniformBounds.owner_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedUniformBounds.owner_cost
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedUniformBounds.post_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedUniformBounds.post_step
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedUniformBounds.post_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedUniformBounds.post_cost
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedUniformBounds.publication_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedUniformBounds.publication_cost
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedUniformBounds.prepare_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedUniformBounds.prepare_cost
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedUniformBounds.complete_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedUniformBounds.complete_cost

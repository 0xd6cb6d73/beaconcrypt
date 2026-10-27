import BeaconcryptCore.Computational.PqxdhLaterSavedPostCompiler

/-! The complete saved descriptor and its original adaptive Post retain explicit selected sealing and raw-opening caps. Source-local work remains a separate inherited resource ledger. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterSavedPostBounds
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
    (prior : Prior) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (monitor : Fin B) (qPost : Nat)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Result Bool S B)
    (material : PqxdhOrderedChainHybrids.Material)
    (fits : PqxdhInitialOriginCertificates.Fits qPost context)
    (state : RawCtxSelectedReceiveCompiler.State (Local A N C))
variable (predicate : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Prop) [DecidablePred predicate]
    (externalZero : ∀ query localState,
      ((PqxdhSelectedCallbackCompiler.lower pre application initial selector aux (.inl query)).run localState).IsQueryBoundP predicate 0)

include externalZero

/-- Actual source erasure and optional serialization use no selected component requests; their own source work is retained. -/
theorem publication_bound (saved : PqxdhInitialBuilderContext.Builder extra M P I D K Result S B)
    (sealed : Option RawCtxSourceSend.Encrypted) (localState : Local A N C) :
    ((PqxdhLaterSavedPostCompiler.publication pre application initial selector aux target sender saved material sealed).run localState).IsQueryBoundP predicate 0 := by
  simp only [PqxdhLaterSavedPostCompiler.publication, PqxdhInitialBuilderContext.afterSend, StateT.run_bind]
  apply isQueryBoundP_bind (m := 0) (externalZero _ localState)
  intro erased _
  cases sealed with
  | none => trivial
  | some encrypted =>
      simp only [StateT.run_bind]
      apply isQueryBoundP_bind (m := 0) (externalZero _ erased.2)
      intro serialized _
      cases serialized.1 <;> trivial

/-- Each saved source request makes at most one request of the selected class before the original Post, including a builder whose publication fails. -/
theorem prepare_bound (localState : Local A N C) :
    (PqxdhLaterSavedPostCompiler.prepare pre application initial selector aux fixed writer prior target nonce next sender read
      qPost context material fits localState).IsQueryBoundP predicate 1 := by
  rcases context with ⟨original, trace, origin⟩
  cases original with
  | inl original =>
      cases original with
      | record request before outside inner =>
          unfold PqxdhLaterSavedPostCompiler.prepare
          exact isQueryBoundP_bind (m := 0)
            (RawCtxSelectedPendingRoleCompiler.live_queries fixed writer prior target nonce next read inner material fits.2).isQueryBoundP
            (fun _ _ => trivial)
      | finish index before control candidate outside inner =>
          unfold PqxdhLaterSavedPostCompiler.prepare
          exact isQueryBoundP_bind (m := 0)
            (RawCtxSelectedPendingOwnerCompiler.owner_queries fixed writer prior target nonce next read inner material fits.2).isQueryBoundP
            (fun _ _ => trivial)
  | inr saved =>
      unfold PqxdhLaterSavedPostCompiler.prepare
      apply isQueryBoundP_bind (m := 0) (RawCtxSelectedPendingSendCompiler.sealing_queries fixed.crypto writer _).isQueryBoundP
      intro sealed _
      exact isQueryBoundP_bind (m := 0)
        (publication_bound pre application initial selector aux target sender material predicate externalZero saved sealed localState)
        (fun _ _ => trivial)

omit externalZero in
/-- Every syntactically possible staged reply carries its original all-reply Post allowance. This is derived from the saved source certificate rather than supplied as a new continuation premise. -/
theorem prepare_post (localState : Local A N C)
    (prepared : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result × InsState M P I D K A N C S B)
    (supported : prepared ∈ support
      (PqxdhLaterSavedPostCompiler.prepare pre application initial selector aux fixed writer prior target nonce next sender read
        qPost context material fits localState)) : prepared.1.IsTotalQueryBound qPost := by
  rcases context with ⟨original, trace, origin⟩
  cases original with
  | inl original =>
      cases original with
      | record request before outside inner =>
          simp only [PqxdhLaterSavedPostCompiler.prepare, mem_support_bind_iff, mem_support_pure_iff] at supported
          obtain ⟨reply, _, rfl⟩ := supported
          exact fits.1 reply.1
      | finish index before control candidate outside inner =>
          simp only [PqxdhLaterSavedPostCompiler.prepare, mem_support_bind_iff, mem_support_pure_iff] at supported
          obtain ⟨reply, _, rfl⟩ := supported
          exact fits.1 _
  | inr saved =>
      simp only [PqxdhLaterSavedPostCompiler.prepare, mem_support_bind_iff, mem_support_pure_iff] at supported
      obtain ⟨sealed, _, published, _, rfl⟩ := supported
      exact fits _

/-- The saved request plus all of its original adaptive Post has cap `1 + qPost` for any component class absent from the source-local callbacks. -/
theorem complete_bound (localState : Local A N C) :
    (PqxdhLaterSavedPostCompiler.complete pre application initial selector aux fixed writer prior target nonce next mark sender route read monitor
      qPost context material fits localState).IsQueryBoundP predicate (1 + qPost) := by
  unfold PqxdhLaterSavedPostCompiler.complete
  apply isQueryBoundP_bind
    (prepare_bound pre application initial selector aux fixed writer prior target nonce next sender read qPost context material fits
      predicate externalZero localState)
  intro prepared supported
  exact insPost_client pre application initial selector aux fixed writer prior
    (some (Entry.mk (PqxdhInitialBuilderContext.address context.original) material)) target nonce next
    sender route read mark monitor predicate
    (insPost_step pre application initial selector aux fixed writer prior
      (some (Entry.mk (PqxdhInitialBuilderContext.address context.original) material)) target nonce next
      sender route read mark monitor predicate externalZero)
    prepared.1 qPost (prepare_post pre application initial selector aux fixed writer prior target nonce next sender read
      qPost context material fits localState prepared supported) prepared.2

omit externalZero in
/-- Actual callback wiring discharges the zero-class premises. The complete saved continuation counts attempted selected seals, raw openings and hash calls, without treating native coins or local primitive work as free. -/
theorem component_bills (localState : Local A N C) :
    (PqxdhLaterSavedPostCompiler.complete pre application initial selector aux fixed writer prior target nonce next mark sender route read monitor
      qPost context material fits localState).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) (1 + qPost) ∧
    (PqxdhLaterSavedPostCompiler.complete pre application initial selector aux fixed writer prior target nonce next mark sender route read monitor
      qPost context material fits localState).IsQueryBoundP
        (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) (1 + qPost) ∧
    (PqxdhLaterSavedPostCompiler.complete pre application initial selector aux fixed writer prior target nonce next mark sender route read monitor
      qPost context material fits localState).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute (1 + qPost) := by
  refine ⟨?_, ?_, ?_⟩
  all_goals apply complete_bound
  · exact PqxdhFirstBeaconRecordCtx.external_no_seal pre application initial selector aux
  · intro query current
    change (simulateQ RawCtxSourceSharedRom.forward
      ((PqxdhSelectedCallbackCompiler.callback pre application initial selector aux query).run current)).IsQueryBoundP _ 0
    exact PqxdhFirstBeaconRecordCtx.forward_no_open _
  · exact PqxdhFirstBeaconRecordCtx.external_no_hash pre application initial selector aux

end BeaconcryptCore.Computational.PqxdhLaterSavedPostBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedPostBounds.publication_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedPostBounds.publication_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedPostBounds.prepare_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedPostBounds.prepare_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedPostBounds.prepare_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedPostBounds.prepare_post
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedPostBounds.complete_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedPostBounds.complete_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedPostBounds.component_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedPostBounds.component_bills

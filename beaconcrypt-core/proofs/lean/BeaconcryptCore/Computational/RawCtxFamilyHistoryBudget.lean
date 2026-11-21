import BeaconcryptCore.Computational.RawCtxFamilyStoppedResources

/-!
The original LIVE source budget follows both the captured disclosure history and the remaining source client. Every prior actual read grows the known-input list by at most one and consumes one reveal coordinate; family/public operations preserve that list. The resulting exact selected context retains a joint prefix-history plus residual-read cap, so the candidate reduction never charges an unbounded saved history or counts the same source reveal twice.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxFamilyHistoryBudget
open RawCtxPendingFamilyLiveTails RawCtxQueryOccurrence RawCtxQueryOccurrenceComposition RawCtxSelectedFamilyContext
open RawCtxFamilyResidualBudget
variable {M P I D K Result : Type} {S B : Nat}

/-- The same actual source-selected frame retains its exact residual source certificate and a single reveal budget shared by prefix disclosures and later reads. -/
theorem source_context
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (budget : Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (prior : List RatchetChain) (state : NativeLive M P I D K S B)
    (query : (LivePrimitiveSpec RatchetChain S B).Domain)
    (next : (LivePrimitiveSpec RatchetChain S B).Range query → OracleComp (LivePrimitiveSpec RatchetChain S B)
      (Result × NativeLive M P I D K S B))
    (occurs : Occurs query next (program sender route decode client state))
    (chosen : selected query = true) :
    ∃ (context : Context M P I D K Result S B) (residual : Budget),
      (⟨query, next⟩ : Frame M P I D K Result S B) = frame sender route decode context ∧
      Below residual budget ∧ Fits residual context ∧
      (RawCtxFamilyFreshnessProxy.knownInputs prior (RawCtxFamilyStoppedResources.history context)).length + residual.2 ≤
        (RawCtxFamilyFreshnessProxy.knownInputs prior state.2).length + budget.2 := by
  induction client using OracleComp.inductionOn generalizing budget state query next with
  | pure value => exact (pure_impossible query next (value, state) occurs).elim
  | query_bind request outside ih =>
    have tailBound : ∀ reply, RawCtxRevealBudgets.Bounded (outside reply) (RawCtxRevealBudgets.remaining request budget) := bounded.2
    have below := remaining_below request budget
    cases request with
    | inl request =>
      rw [program_original sender route decode request outside state] at occurs
      change Occurs query next (simulateQ inlForward
        ((RawCtxGenericFamilyFrontend.impl RawCtxPendingOwnerQueries.calls RawCtxPendingOwnerQueries.publicForward
          sender route decode request).run state.1) >>= afterFamily sender route decode state.2 outside) at occurs
      rcases bind_cases query next _ _ occurs with ⟨inner, inside, continuation⟩ | ⟨result, after⟩
      · rcases inl_cases query inner _ inside with ⟨originalQuery, originalNext, originalOccurs, same⟩
        have sameQuery := congrArg Sigma.fst same
        change query = .inl originalQuery at sameQuery
        have selectedOriginal : RawCtxPendingMixedPrefix.ownerSelected originalQuery = true := by
          simpa only [sameQuery, selected] using chosen
        obtain ⟨context, originalFrame, quiet⟩ := RawCtxQuietFamilyTails.single_tail sender route decode request state.1
          originalQuery originalNext (by simpa only [RawCtxPendingFamilyTails.program, simulateQ_spec_query] using originalOccurs) selectedOriginal
        refine ⟨.family request state.2 outside context, RawCtxRevealBudgets.remaining (.inl request) budget, ?_, below,
          ⟨RawCtxRevealBudgets.remaining (.inl request) budget, ⟨fun _ => le_refl _, le_refl _⟩, tailBound, quiet⟩, le_refl _⟩
        rw [continuation]
        have first := congrArg (fun pair : Σ q, (LivePrimitiveSpec RatchetChain S B).Range q →
          OracleComp (LivePrimitiveSpec RatchetChain S B)
            ((RawCtxProtocolRoles.SourceSpec S B).Range request × NativeFamily M P I D K S B) =>
              (⟨pair.1, fun reply => pair.2 reply >>= afterFamily sender route decode state.2 outside⟩ : Frame M P I D K Result S B)) same
        exact first.trans (congrArg (fun saved : FamilyFrame M P I D K ((RawCtxProtocolRoles.SourceSpec S B).Range request) S B =>
          (⟨.inl saved.1, fun reply => liftFamily sender route decode state.2 outside (saved.2 reply)⟩ : Frame M P I D K Result S B)) originalFrame)
      · obtain ⟨context, residual, frame, smaller, fits, historyBound⟩ := ih result.1 _ (tailBound result.1)
          (result.2, RawCtxProtocolReveals.tick state.2) query next after chosen
        exact ⟨context, residual, frame, ⟨fun kind => le_trans (smaller.1 kind) (below.1 kind), le_trans smaller.2 below.2⟩, fits, historyBound⟩
    | inr request =>
      rw [program_read sender route decode request outside state] at occurs
      rcases query_cases query (.inr (request, RawCtxGenericRoleFamily.selectedKernel (RawCtxGenericFamilyRead.requestOwner request) state.1)) next _ occurs
        with same | ⟨reply, after⟩
      · have sameQuery := congrArg Sigma.fst same
        change query = .inr (request, RawCtxGenericRoleFamily.selectedKernel (RawCtxGenericFamilyRead.requestOwner request) state.1) at sameQuery
        rw [sameQuery] at chosen
        cases chosen
      · obtain ⟨context, residual, frame, smaller, fits, historyBound⟩ := ih reply _ (tailBound reply)
          (state.1, RawCtxProtocolReveals.note ⟨request, reply⟩ state.2) query next after chosen
        refine ⟨context, residual, frame, ⟨fun kind => le_trans (smaller.1 kind) (below.1 kind), le_trans smaller.2 below.2⟩, fits, ?_⟩
        have growth := RawCtxFamilyFreshnessProxy.knownInputs_note_length prior state.2 ⟨request, reply⟩
        have positive : 0 < budget.2 := bounded.1
        simp only [RawCtxRevealBudgets.remaining] at historyBound
        omega

/-- The actual source prefix and residual observer share one reveal allowance in the complete candidate bound, before every later handler and material choice. -/
theorem source_candidates
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (budget : Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (prior : List RatchetChain) (state : NativeLive M P I D K S B)
    (query : (LivePrimitiveSpec RatchetChain S B).Domain)
    (next : (LivePrimitiveSpec RatchetChain S B).Range query → OracleComp (LivePrimitiveSpec RatchetChain S B)
      (Result × NativeLive M P I D K S B))
    (occurs : Occurs query next (program sender route decode client state))
    (chosen : selected query = true) :
    ∃ context : Context M P I D K Result S B,
      (⟨query, next⟩ : Frame M P I D K Result S B) = frame sender route decode context ∧ Fits budget context ∧
      ∀ (PrimitiveState : Type)
        (handler : QueryImpl RawCtxSelectedLiveCompiler.Spec (StateT PrimitiveState ProbComp))
        (direct : RawCtxSelectedLiveCompiler.Spec.Domain → Bool)
        (earlier : List PqxdhSecretInputKdf.RootOutput) (primitive : PrimitiveState) (value : PqxdhOrderedChainHybrids.Material)
        (result : (Result × RawCtxPendingFamilyLiveQueries.State RawCtxSelectedChain.Slot M P I D K S B) ×
          ((PrimitiveState × List PqxdhSecretInputKdf.RootOutput) × Bool)),
        result ∈ support ((simulateQ
          (RawCtxFlaggedQueryTrace.trace handler RawCtxSelectedLiveCompiler.inputs direct)
          (simulateQ RawCtxFamilyPendingCompiler.live (stopped sender route decode context value))).run
            ((primitive, RawCtxFamilyFreshnessProxy.knownInputs prior (RawCtxFamilyStoppedResources.history context) ++ earlier), false)) →
        result.2.1.2.length ≤ (RawCtxFamilyFreshnessProxy.knownInputs prior state.2).length + earlier.length +
          (254 + (budget.1 .send + 51 * budget.1 .raw) + budget.1 .hkdf + budget.2) := by
  obtain ⟨context, residual, same, below, fits, historyBound⟩ :=
    source_context sender route decode client budget bounded prior state query next occurs chosen
  refine ⟨context, same, fits_mono residual budget below context fits, ?_⟩
  intro PrimitiveState handler direct earlier primitive value result supported
  have cap := RawCtxFamilyStoppedResources.history_candidates handler direct sender route decode context residual fits value
    prior earlier primitive result supported
  have send := below.1 .send
  have raw := below.1 .raw
  have hkdf := below.1 .hkdf
  omega

end BeaconcryptCore.Computational.RawCtxFamilyHistoryBudget

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyHistoryBudget.source_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyHistoryBudget.source_context

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyHistoryBudget.source_candidates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyHistoryBudget.source_candidates

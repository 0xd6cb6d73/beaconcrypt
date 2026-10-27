import BeaconcryptCore.Computational.RawCtxQuietFamilyTails
import BeaconcryptCore.Computational.RawCtxRevealBudgets

/-!
The actual bounded LIVE source derives its selected dependent frame, quiet inner family and coordinatewise smaller outside-client budget together. Every possible reply and original history transition is retained. No budget for an arbitrary captured Context, cryptographic assumption, freshness condition or cache-miss premise is inserted; pending completion costs remain separate.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxFamilyResidualBudget
open RawCtxPendingFamilyLiveTails RawCtxQueryOccurrence RawCtxQueryOccurrenceComposition RawCtxSelectedFamilyContext

abbrev Budget := RawCtxRevealBudgets.Budget

def Below (small large : Budget) : Prop := (∀ kind, small.1 kind ≤ large.1 kind) ∧ small.2 ≤ large.2

/-- Consuming any original source request never increases any of its six query coordinates. -/
theorem remaining_below {S B : Nat} (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (budget : Budget) :
    Below (RawCtxRevealBudgets.remaining query budget) budget := by
  cases query with
  | inl request =>
    constructor
    · intro kind
      simp only [RawCtxRevealBudgets.remaining, RawCtxServerServiceBounds.remaining]
      by_cases same : RawCtxProtocolBudgets.sourceKind request = kind
      · subst kind
        simp only [Function.update_self, Nat.sub_le]
      · simp only [Function.update_of_ne (Ne.symm same), le_refl]
    · exact le_refl _
  | inr request => exact ⟨fun _ => le_refl _, Nat.sub_le _ _⟩

variable {M P I D K Result : Type} {S B : Nat}

def Fits (budget : Budget) : Context M P I D K Result S B → Prop
  | .family _ _ outside inner =>
      ∃ residual : Budget, Below residual budget ∧
        (∀ reply, RawCtxRevealBudgets.Bounded (outside reply) residual) ∧ RawCtxQuietFamilyTails.Quiet inner

/-- A smaller actual residual certificate also fits every coordinatewise larger source budget. -/
theorem fits_mono (small large : Budget) (below : Below small large)
    (context : Context M P I D K Result S B) (fits : Fits small context) : Fits large context := by
  cases context with
  | family request history outside inner =>
    rcases fits with ⟨residual, bounded, source, quiet⟩
    exact ⟨residual, ⟨fun kind => le_trans (bounded.1 kind) (below.1 kind), le_trans bounded.2 below.2⟩, source, quiet⟩

/-- The original bounded LIVE source derives the exact selected frame, quiet inner family and a coordinatewise smaller residual outside-client budget. -/
theorem program_context
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (budget : Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : NativeLive M P I D K S B)
    (query : (LivePrimitiveSpec RatchetChain S B).Domain)
    (next : (LivePrimitiveSpec RatchetChain S B).Range query → OracleComp (LivePrimitiveSpec RatchetChain S B)
      (Result × NativeLive M P I D K S B))
    (occurs : Occurs query next (program sender route decode client state))
    (chosen : selected query = true) :
    ∃ context : Context M P I D K Result S B,
      (⟨query, next⟩ : Frame M P I D K Result S B) = frame sender route decode context ∧ Fits budget context := by
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
        refine ⟨.family request state.2 outside context, ?_, RawCtxRevealBudgets.remaining (.inl request) budget, below, tailBound, quiet⟩
        rw [continuation]
        have first := congrArg (fun pair : Σ q, (LivePrimitiveSpec RatchetChain S B).Range q →
          OracleComp (LivePrimitiveSpec RatchetChain S B)
            ((RawCtxProtocolRoles.SourceSpec S B).Range request × NativeFamily M P I D K S B) =>
              (⟨pair.1, fun reply => pair.2 reply >>= afterFamily sender route decode state.2 outside⟩ : Frame M P I D K Result S B)) same
        exact first.trans (congrArg (fun saved : FamilyFrame M P I D K ((RawCtxProtocolRoles.SourceSpec S B).Range request) S B =>
          (⟨.inl saved.1, fun reply => liftFamily sender route decode state.2 outside (saved.2 reply)⟩ : Frame M P I D K Result S B)) originalFrame)
      · obtain ⟨context, frame, fits⟩ := ih result.1 _ (tailBound result.1)
          (result.2, RawCtxProtocolReveals.tick state.2) query next after chosen
        exact ⟨context, frame, fits_mono _ budget below context fits⟩
    | inr request =>
      rw [program_read sender route decode request outside state] at occurs
      rcases query_cases query (.inr (request, RawCtxGenericRoleFamily.selectedKernel (RawCtxGenericFamilyRead.requestOwner request) state.1)) next _ occurs
        with same | ⟨reply, after⟩
      · have sameQuery := congrArg Sigma.fst same
        change query = .inr (request, RawCtxGenericRoleFamily.selectedKernel (RawCtxGenericFamilyRead.requestOwner request) state.1) at sameQuery
        rw [sameQuery] at chosen
        cases chosen
      · obtain ⟨context, frame, fits⟩ := ih reply _ (tailBound reply)
          (state.1, RawCtxProtocolReveals.note ⟨request, reply⟩ state.2) query next after chosen
        exact ⟨context, frame, fits_mono _ budget below context fits⟩

/-- Every concrete nonnegative query bill is bounded by the corresponding original source bill. -/
theorem bill_mono (cost : RawCtxServerServiceBounds.Kind → Nat) (readCost : Nat)
    (small large : Budget) (below : Below small large) :
    RawCtxRevealBudgets.bill cost readCost small ≤ RawCtxRevealBudgets.bill cost readCost large := by
  exact Nat.add_le_add (Finset.sum_le_sum (fun kind _ => Nat.mul_le_mul_left _ (below.1 kind)))
    (Nat.mul_le_mul_left _ below.2)

/-- A supported selected prefix of the bounded original LIVE program derives the same resource-certified context and preserves its reached primitive state. -/
theorem reached_context {PrimitiveState : Type}
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (budget : Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : NativeLive M P I D K S B)
    (impl : QueryImpl (LivePrimitiveSpec RatchetChain S B) (StateT PrimitiveState ProbComp))
    (index : Nat) (initial reached : PrimitiveState)
    (query : (LivePrimitiveSpec RatchetChain S B).Domain)
    (next : (LivePrimitiveSpec RatchetChain S B).Range query → OracleComp (LivePrimitiveSpec RatchetChain S B)
      (Result × NativeLive M P I D K S B))
    (supported : (RawCtxPendingMixedPrefix.Stopped.pending query next, reached) ∈ support
      (RawCtxPendingMixedPrefix.scan selected impl (program sender route decode client state) index initial)) :
    ∃ context : Context M P I D K Result S B,
      (⟨query, next⟩ : Frame M P I D K Result S B) = frame sender route decode context ∧ Fits budget context := by
  exact program_context sender route decode client budget bounded state query next
    (scan_occurs selected impl _ index initial reached query next supported)
    (RawCtxPendingMixedPrefix.pending_selected selected impl _ index initial reached query next supported)

end BeaconcryptCore.Computational.RawCtxFamilyResidualBudget

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyResidualBudget.remaining_below' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyResidualBudget.remaining_below

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyResidualBudget.fits_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyResidualBudget.fits_mono

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyResidualBudget.program_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyResidualBudget.program_context

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyResidualBudget.bill_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyResidualBudget.bill_mono

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyResidualBudget.reached_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyResidualBudget.reached_context

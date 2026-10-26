import BeaconcryptCore.Computational.RawCtxFamilyCompletionBudgets
import BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets

/-!
The actual stopped family observer has a source-derived uniform cap U+64(S+R+H+1) and candidate growth at most 254+S+51R+K+E. The complete initial history and earlier candidate list remain explicit, including duplicates. The original bounded selected source constructs the same context before later material and observer choices; these are resource statements, not security or freshness assumptions.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxFamilyStoppedResources
open RawCtxSelectedChain RawCtxSelectedFamilyContext RawCtxFamilyPrimitiveBudgets RawCtxFamilyCompletionBudgets
open PqxdhOrderedChainHybrids PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
variable {M P I D K Result : Type} {S B : Nat}

/-- The actual material-only family observer pays U+64(S+R+H+1), including its entire pending completion and all original outside source requests. -/
theorem uniform {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (output : FullOutput) (reader : RawCtxSelectedLiveTrace.Reader) (view : RawCtxSelectedParentLive.View)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context M P I D K Result S B) (budget : RawCtxRevealBudgets.Budget)
    (fits : RawCtxFamilyResidualBudget.Fits budget context) (value : Material)
    (state : RawCtxSelectedParentLive.State Auxiliary) :
    ((simulateQ (RawCtxSelectedParentReadMask.observed source writer prior entry output reader view)
      (simulateQ RawCtxFamilyPendingCompiler.live (stopped sender route decode context value))).run state).IsTotalQueryBound
      (budget.1 .coin + 64 * (budget.1 .send + budget.1 .raw + budget.1 .hash + 1)) := by
  have cap := RawCtxFamilyObservationBudgets.complete_uniform source writer prior entry output reader view
    _ (fun selected => contextReserve context selected + sourceCost selected budget)
    (stopped_class sender route decode context budget fits value) state
  apply cap.mono
  rcases reserve_shape context with receive | send
  · simp only [receive, receiveReserve, sourceCost]
    omega
  · simp only [send, sendReserve, sourceCost]
    omega

/-- Every adaptive supported candidate trace pays its complete initial prefix and at most 254+S+51R+K+E new entries; repeated guesses and failed attempts remain counted. -/
theorem candidates {PrimitiveState : Type}
    (handler : QueryImpl RawCtxSelectedLiveCompiler.Spec (StateT PrimitiveState ProbComp))
    (direct : RawCtxSelectedLiveCompiler.Spec.Domain → Bool)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context M P I D K Result S B) (budget : RawCtxRevealBudgets.Budget)
    (fits : RawCtxFamilyResidualBudget.Fits budget context) (value : Material)
    (state : (PrimitiveState × List RootOutput) × Bool)
    (result : (Result × RawCtxPendingFamilyLiveQueries.State Slot M P I D K S B) × ((PrimitiveState × List RootOutput) × Bool))
    (supported : result ∈ support ((simulateQ
      (RawCtxFlaggedQueryTrace.trace handler RawCtxSelectedLiveCompiler.inputs direct)
      (simulateQ RawCtxFamilyPendingCompiler.live (stopped sender route decode context value))).run state)) :
    result.2.1.2.length ≤ state.1.2.length + (254 + (budget.1 .send + 51 * budget.1 .raw) + budget.1 .hkdf + budget.2) := by
  have cap := RawCtxFamilyObservationBudgets.trace_length handler direct _
    (fun selected => contextReserve context selected + sourceCost selected budget)
    (stopped_class sender route decode context budget fits value) state result supported
  rcases reserve_shape context with receive | send
  · simpa only [receive, receiveReserve, sourceCost, Nat.zero_add, Nat.add_assoc] using cap
  · simp only [send, sendReserve, sourceCost, Nat.zero_add] at cap
    omega

def history (context : Context M P I D K Result S B) : RawCtxProtocolReveals.History S B :=
  match context with
  | .family _ saved _ _ => saved

/-- Initializing the freshness observer from the actual saved history pays every prior disclosed value and earlier candidate, with duplicates preserved. -/
theorem history_candidates {PrimitiveState : Type}
    (handler : QueryImpl RawCtxSelectedLiveCompiler.Spec (StateT PrimitiveState ProbComp))
    (direct : RawCtxSelectedLiveCompiler.Spec.Domain → Bool)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context M P I D K Result S B) (budget : RawCtxRevealBudgets.Budget)
    (fits : RawCtxFamilyResidualBudget.Fits budget context) (value : Material)
    (prior : List RatchetChain) (earlier : List RootOutput) (state : PrimitiveState)
    (result : (Result × RawCtxPendingFamilyLiveQueries.State Slot M P I D K S B) × ((PrimitiveState × List RootOutput) × Bool))
    (supported : result ∈ support ((simulateQ
      (RawCtxFlaggedQueryTrace.trace handler RawCtxSelectedLiveCompiler.inputs direct)
      (simulateQ RawCtxFamilyPendingCompiler.live (stopped sender route decode context value))).run
        ((state, RawCtxFamilyFreshnessProxy.knownInputs prior (history context) ++ earlier), false))) :
    result.2.1.2.length ≤ (RawCtxFamilyFreshnessProxy.knownInputs prior (history context)).length + earlier.length +
      (254 + (budget.1 .send + 51 * budget.1 .raw) + budget.1 .hkdf + budget.2) := by
  simpa only [List.length_append] using candidates handler direct sender route decode context budget fits value
    ((state, RawCtxFamilyFreshnessProxy.knownInputs prior (history context) ++ earlier), false) result supported

/-- The same original bounded source-selected frame constructs its observer before every later material, output, reader and private-state choice, with the explicit uniform cap already discharged. -/
theorem source_context
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : NativeLive M P I D K S B)
    (query : (LivePrimitiveSpec RatchetChain S B).Domain)
    (next : (LivePrimitiveSpec RatchetChain S B).Range query → OracleComp (LivePrimitiveSpec RatchetChain S B)
      (Result × NativeLive M P I D K S B))
    (occurs : RawCtxQueryOccurrence.Occurs query next (RawCtxPendingFamilyLiveTails.program sender route decode client state))
    (chosen : RawCtxPendingFamilyLiveTails.selected query = true) :
    ∃ context : Context M P I D K Result S B,
      (⟨query, next⟩ : Frame M P I D K Result S B) = frame sender route decode context ∧
      RawCtxFamilyResidualBudget.Fits budget context ∧
      ∀ (Auxiliary : Type) (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
        (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
        (output : FullOutput) (reader : RawCtxSelectedLiveTrace.Reader) (view : RawCtxSelectedParentLive.View)
        (value : Material) (primitive : RawCtxSelectedParentLive.State Auxiliary),
        ((simulateQ (RawCtxSelectedParentReadMask.observed source writer prior entry output reader view)
          (simulateQ RawCtxFamilyPendingCompiler.live (stopped sender route decode context value))).run primitive).IsTotalQueryBound
          (budget.1 .coin + 64 * (budget.1 .send + budget.1 .raw + budget.1 .hash + 1)) := by
  obtain ⟨context, same, fits⟩ := RawCtxFamilyResidualBudget.program_context sender route decode client budget bounded state query next occurs chosen
  exact ⟨context, same, fits, fun _ source writer prior entry output reader view value primitive =>
    uniform source writer prior entry output reader view sender route decode context budget fits value primitive⟩

end BeaconcryptCore.Computational.RawCtxFamilyStoppedResources

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyStoppedResources.uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyStoppedResources.uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyStoppedResources.candidates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyStoppedResources.candidates

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyStoppedResources.history_candidates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyStoppedResources.history_candidates

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyStoppedResources.source_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyStoppedResources.source_context

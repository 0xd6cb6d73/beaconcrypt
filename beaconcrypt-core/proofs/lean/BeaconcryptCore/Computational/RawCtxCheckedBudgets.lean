import BeaconcryptCore.Computational.RawCtxCheckedParentSecrecy
import BeaconcryptCore.Computational.RawCtxFamilyStoppedResources

/-!
The private finite lineage checker adds at most n+1 actual private derivation callbacks after the entire original source observer. It adds no network, opening, sealing, public HKDF, read or random-sampling request. Those private evaluations and candidate entries are explicitly charged local reduction work. Original source and pending-completion budgets are retained through the same stopped family program.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxCheckedBudgets
open RawCtxSelectedChain RawCtxFamilyPrimitiveBudgets RawCtxFamilyLineageCompletion RawCtxSelectedFamilyContext
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids
variable {M P I D K A : Type} {S B : Nat}

/-- Each checker request is one private derivation and no other primitive class; it uses the same existing receive derivation interface. -/
theorem forward_class (input : Slot) (selected : Class) :
    (forward input).IsQueryBoundP (fun query => liveClass query = selected)
      (if selected = .kdf then 1 else 0) := by
  simp [forward, derivation, QueryImpl.compose, RawCtxSelectedLiveCompiler.primitiveForward,
    liveClass, primitiveClass, eq_comm]
  intro equal
  subst selected
  simp

/-- The entire finite checker pays exactly its reserved private-callback cap, with zero callbacks in every other class. -/
theorem checker_class (n : Nat) (selected : Class) :
    (checker n).IsQueryBoundP (fun query => liveClass query = selected)
      (if selected = .kdf then n + 1 else 0) := by
  apply RawCtxSourceOpen.simulate_bound forward (fun _ => selected = .kdf)
    (fun query => liveClass query = selected)
  · by_cases selected = .kdf
    all_goals simp_all only [ite_true, ite_false]
    · exact (RawCtxFiniteLineageCheck.queries RawCtxFiniteLineageCheck.labelKey n Slot.hidden).isQueryBoundP
    · exact isQueryBoundP_false _ 0
  · exact fun query => forward_class query selected

noncomputable def checkedStopped {Result : Type}
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context M P I D K Result S B) (value : Material) (n : Nat) := do
  let original ← simulateQ RawCtxFamilyPendingCompiler.live (stopped sender route decode context value)
  let lineage ← checker n
  pure (original, lineage)

/-- One actual carried source context plus its appended finite checker pays the original pending reserve, all outside requests, and n+1 extra private derivations. -/
theorem stopped_class {Result : Type}
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context M P I D K Result S B) (budget : RawCtxRevealBudgets.Budget)
    (fits : RawCtxFamilyResidualBudget.Fits budget context) (value : Material) (n : Nat) (selected : Class) :
    (checkedStopped sender route decode context value n).IsQueryBoundP
      (fun query => liveClass query = selected)
      ((RawCtxFamilyCompletionBudgets.contextReserve context selected + sourceCost selected budget) +
        (if selected = .kdf then n + 1 else 0)) := by
  apply isQueryBoundP_bind (RawCtxFamilyCompletionBudgets.stopped_class sender route decode context budget fits value selected)
  intro result _
  simpa only [bind_pure_comp, isQueryBoundP_map_iff] using checker_class n selected

/-- Appending the deterministic finite checker adds no uniform sampling to the exact stopped observer, including all original commitment work. -/
theorem uniform {Result Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (output : FullOutput) (reader : RawCtxSelectedLiveTrace.Reader) (view : RawCtxSelectedParentLive.View)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context M P I D K Result S B) (budget : RawCtxRevealBudgets.Budget)
    (fits : RawCtxFamilyResidualBudget.Fits budget context) (value : Material) (n : Nat)
    (state : RawCtxSelectedParentLive.State Auxiliary) :
    ((simulateQ (RawCtxSelectedParentReadMask.observed source writer prior entry output reader view)
      (checkedStopped sender route decode context value n)).run state).IsTotalQueryBound
      (budget.1 .coin + 64 * (budget.1 .send + budget.1 .raw + budget.1 .hash + 1)) := by
  have cap := RawCtxFamilyObservationBudgets.complete_uniform source writer prior entry output reader view _
    (fun selected => (RawCtxFamilyCompletionBudgets.contextReserve context selected + sourceCost selected budget) +
      (if selected = .kdf then n + 1 else 0))
    (stopped_class sender route decode context budget fits value n) state
  apply cap.mono
  rcases RawCtxFamilyCompletionBudgets.reserve_shape context with receive | send
  · simp [receive, RawCtxFamilyCompletionBudgets.receiveReserve, sourceCost]
    omega
  · simp [send, RawCtxFamilyCompletionBudgets.sendReserve, sourceCost]
    omega

/-- The complete source-and-checker candidate ledger charges every original entry, all source requests and all n+1 possible private checker inputs, retaining duplicates. -/
theorem candidates {Result PrimitiveState : Type}
    (handler : QueryImpl RawCtxSelectedLiveCompiler.Spec (StateT PrimitiveState ProbComp))
    (direct : RawCtxSelectedLiveCompiler.Spec.Domain → Bool)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context M P I D K Result S B) (budget : RawCtxRevealBudgets.Budget)
    (fits : RawCtxFamilyResidualBudget.Fits budget context) (value : Material) (n : Nat)
    (state : (PrimitiveState × List RootOutput) × Bool)
    (result : ((Result × RawCtxPendingFamilyLiveQueries.State Slot M P I D K S B) × List Slot) × ((PrimitiveState × List RootOutput) × Bool))
    (supported : result ∈ support ((simulateQ
      (RawCtxFlaggedQueryTrace.trace handler RawCtxSelectedLiveCompiler.inputs direct)
      (checkedStopped sender route decode context value n)).run state)) :
    result.2.1.2.length ≤ state.1.2.length +
      (254 + (budget.1 .send + 51 * budget.1 .raw) + budget.1 .hkdf + budget.2 + (n + 1)) := by
  have cap := RawCtxFamilyObservationBudgets.trace_length handler direct _
    (fun selected => (RawCtxFamilyCompletionBudgets.contextReserve context selected + sourceCost selected budget) +
      (if selected = .kdf then n + 1 else 0))
    (stopped_class sender route decode context budget fits value n) state result supported
  rcases RawCtxFamilyCompletionBudgets.reserve_shape context with receive | send
  · simpa [receive, RawCtxFamilyCompletionBudgets.receiveReserve, sourceCost, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using cap
  · simp [send, RawCtxFamilyCompletionBudgets.sendReserve, sourceCost] at cap
    omega

/-- The source-carried context is exactly the type-dependent original completion consumed by the checked secrecy reduction. No inverse of the frame map is selected. -/
theorem source_checked
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (history : RawCtxProtocolReveals.History S B)
    (outside : (RawCtxProtocolRoles.SourceSpec S B).Range request → OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool)
    (inner : FamilyContext M P I D K ((RawCtxProtocolRoles.SourceSpec S B).Range request) S B)
    (value : Material) (n : Nat) :
    checkedStopped sender route decode (.family request history outside inner) value n =
      checked sender route decode history outside
        (simulateQ RawCtxPendingOwnerQueries.erase (familyStopped sender route decode inner value)) n := by
  simp only [checkedStopped, RawCtxFamilyPendingCompiler.stopped_source, checked]

/-- The saved disclosure history and earlier candidate list are both charged before any original residual source or checker operation. -/
theorem history_candidates {Result PrimitiveState : Type}
    (handler : QueryImpl RawCtxSelectedLiveCompiler.Spec (StateT PrimitiveState ProbComp))
    (direct : RawCtxSelectedLiveCompiler.Spec.Domain → Bool)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (context : Context M P I D K Result S B) (budget : RawCtxRevealBudgets.Budget)
    (fits : RawCtxFamilyResidualBudget.Fits budget context) (value : Material) (n : Nat)
    (prior : List RatchetChain) (earlier : List RootOutput) (state : PrimitiveState)
    (result : ((Result × RawCtxPendingFamilyLiveQueries.State Slot M P I D K S B) × List Slot) × ((PrimitiveState × List RootOutput) × Bool))
    (supported : result ∈ support ((simulateQ
      (RawCtxFlaggedQueryTrace.trace handler RawCtxSelectedLiveCompiler.inputs direct)
      (checkedStopped sender route decode context value n)).run
        ((state, RawCtxFamilyFreshnessProxy.knownInputs prior (RawCtxFamilyStoppedResources.history context) ++ earlier), false))) :
    result.2.1.2.length ≤ (RawCtxFamilyFreshnessProxy.knownInputs prior (RawCtxFamilyStoppedResources.history context)).length + earlier.length +
      (254 + (budget.1 .send + 51 * budget.1 .raw) + budget.1 .hkdf + budget.2 + (n + 1)) := by
  simpa only [List.length_append] using candidates handler direct sender route decode context budget fits value n
    ((state, RawCtxFamilyFreshnessProxy.knownInputs prior (RawCtxFamilyStoppedResources.history context) ++ earlier), false) result supported

end BeaconcryptCore.Computational.RawCtxCheckedBudgets

/-- info: 'BeaconcryptCore.Computational.RawCtxCheckedBudgets.forward_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCheckedBudgets.forward_class

/-- info: 'BeaconcryptCore.Computational.RawCtxCheckedBudgets.checker_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCheckedBudgets.checker_class

/-- info: 'BeaconcryptCore.Computational.RawCtxCheckedBudgets.stopped_class' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCheckedBudgets.stopped_class

/-- info: 'BeaconcryptCore.Computational.RawCtxCheckedBudgets.uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCheckedBudgets.uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxCheckedBudgets.candidates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCheckedBudgets.candidates

/-- info: 'BeaconcryptCore.Computational.RawCtxCheckedBudgets.source_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCheckedBudgets.source_checked

/-- info: 'BeaconcryptCore.Computational.RawCtxCheckedBudgets.history_candidates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxCheckedBudgets.history_candidates

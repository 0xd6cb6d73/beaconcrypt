import BeaconcryptCore.Computational.PqxdhSelectedMessageSourceFreshness

/-! The original final later-record checker is evaluated through its actual partial-routing source interpreter. Its only step returns the selected full76 material and changes no callback, candidate or disclosure state. This exposes the message-key component of the same final source freshness event. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhSelectedMessageChecker
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids RawCtxFreshChainCut
open PqxdhJointKdfGame PqxdhInitialBeaconAmbient PqxdhInitialParentObserverCompiler PqxdhInitialParentObserver
variable {ι I D K X Response Shared A N C : Type} {extra : OracleSpec ι}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry) (output : FullOutput)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C InitialReply)
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))

/-- The actual hidden-input final check returns the selected full response without adding a known candidate, revealing it or changing any source state. -/
theorem hidden_step (target : RootOutput) (state : (State A N C × List RootOutput) × Bool) :
    (simulateQ
      (PqxdhInitialParentPrivateObserver.observed source writer prior entry output pre application initial selector aux
        (RawCtxSelectedLiveTrace.nativeReader (concreteChain target)) target)
      (PqxdhInitialParentStoppedHop.checkerCompiler .hidden)).run state =
      pure ((RawCtxSelectedChain.Slot.known (concreteChain (nextChain output)), concreteMaterial (material output)), state) := by
  change ((PqxdhInitialParentPrivateObserver.observed source writer prior entry output pre application initial selector aux
    (RawCtxSelectedLiveTrace.nativeReader (concreteChain target)) target)
    (.inl (.inl (.inr (.inl (.inl .hidden)))))).run state = _
  simp only [PqxdhInitialParentPrivateObserver.observed, RawCtxFlaggedQueryTrace.trace, StateT.run,
    PqxdhInitialParentPrivateObserver.old_source]
  rw [RawCtxSelectedParentPrivate.hidden_send]
  simp only [RawCtxSelectedParentTable.step, decoded_parts]
  change (pure ((RawCtxSelectedChain.Slot.known (concreteChain (nextChain output)), concreteMaterial (material output)),
    ((state.1.1, state.1.2 ++ []), state.2 || false)) : ProbComp _) = _
  simp only [List.append_nil, Bool.or_false, Prod.mk.eta]

/-- The final later-record checker executes its literal one source derivation and returns exactly the input marker and selected message-key bytes, with the entire instrumentation unchanged. -/
theorem zero (target : RootOutput) (state : (State A N C × List RootOutput) × Bool) :
    (simulateQ
      (PqxdhInitialParentPrivateObserver.observed source writer prior entry output pre application initial selector aux
        (RawCtxSelectedLiveTrace.nativeReader (concreteChain target)) target)
      (PqxdhInitialParentStoppedHop.checker (some 0))).run state =
      pure ([RawCtxSelectedChain.Slot.hidden, .known (concreteChain (material output).1)], state) := by
  change (do
    let result ← (simulateQ
      (PqxdhInitialParentPrivateObserver.observed source writer prior entry output pre application initial selector aux
        (RawCtxSelectedLiveTrace.nativeReader (concreteChain target)) target)
      (PqxdhInitialParentStoppedHop.checkerCompiler .hidden)).run state
    pure ([RawCtxSelectedChain.Slot.hidden, RawCtxFiniteLineageCheck.labelKey result.1.2], result.2)) = _
  rw [hidden_step, pure_bind]
  rfl

/-- Every actually supported full source run at remaining depth zero returns the literal selected-key checker list. This derives the list from the source interpreter, not a final freshness premise. -/
theorem returned_zero {M P Result Origin Context : Type} {S B : Nat}
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (continuation : PqxdhInitialParentStoppedHop.Continuation Context extra M P I D K X Response Shared A N C Result Origin S B)
    (context : Context × RawCtxSelectedParentEntry.Entry) (target : RootOutput)
    (disclosed : List RatchetChain) (state : State A N C) (candidates : List RootOutput)
    (depth : continuation.depth context.1 = some 0)
    (result : PqxdhInitialParentStoppedHop.Trace M P I D K A N C Result Origin S B)
    (supported : result ∈ support (PqxdhInitialPrivateCheckedFreshness.nativeRun source writer mark sender route decode
      continuation context target output disclosed state candidates)) :
    result.1.2 = [RawCtxSelectedChain.Slot.hidden, .known (concreteChain (material output).1)] := by
  simp only [PqxdhInitialPrivateCheckedFreshness.nativeRun, PqxdhInitialParentStoppedHop.program,
    simulateQ_bind, StateT.run_bind, mem_support_bind_iff, simulateQ_pure, StateT.run_pure,
    mem_support_pure_iff] at supported
  obtain ⟨original, _, tail, reached, rfl⟩ := supported
  rw [depth, zero] at reached
  obtain rfl := OracleComp.eq_of_mem_support_pure _ reached
  rfl

/-- The actual later-record source decision at its final material cut keeps the same gate and complete ancestor list, and splits its actual byte freshness into explicit stopping, known checks and a candidate hit. -/
theorem decision_factor {M P Result Origin Context : Type} {S B : Nat}
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (continuation : PqxdhInitialParentStoppedHop.Continuation Context extra M P I D K X Response Shared A N C Result Origin S B)
    (context : Context × RawCtxSelectedParentEntry.Entry) (target : RootOutput)
    (earlier disclosed : List RatchetChain) (state : State A N C) (candidates : List RootOutput)
    (depth : continuation.depth context.1 = some 0)
    (gate : PqxdhInitialParentStoppedHop.Trace M P I D K A N C Result Origin S B → Prop)
    (result : PqxdhInitialParentStoppedHop.Trace M P I D K A N C Result Origin S B)
    (supported : result ∈ support (PqxdhInitialPrivateCheckedFreshness.nativeRun source writer mark sender route decode
      continuation context target output disclosed state candidates))
    (history : RawCtxSelectedMessageFreshness.History S B)
    (historyEq : result.1.1.2.1.roles.2 = RawCtxSelectedMessageFreshness.interpretHistory (material output).1 history) :
    PqxdhInitialPrivateCheckedFreshness.actualDecision target earlier disclosed gate result = true ↔
      gate result ∧ RawCtxSelectedMessageFreshness.hidden history = false ∧
        RawCtxLiveLineage.FreshValues (concreteChain target :: earlier) (RawCtxSelectedMessageFreshness.known disclosed history) ∧
        concreteChain (material output).1 ∉ RawCtxSelectedMessageFreshness.known disclosed history := by
  simp only [PqxdhInitialPrivateCheckedFreshness.actualDecision, decide_eq_true_eq]
  rw [returned_zero source writer output mark sender route decode continuation context target disclosed state candidates depth result supported,
    historyEq]
  change (gate result ∧ RawCtxLiveLineage.Fresh
    ([concreteChain target, concreteChain (material output).1] ++ earlier) disclosed
      (RawCtxSelectedMessageFreshness.interpretHistory (material output).1 history)) ↔ _
  rw [← PqxdhSelectedMessageSourceFreshness.first_lineage (continuation.prior context.1) target output,
    PqxdhSelectedMessageSourceFreshness.first_fresh]

end BeaconcryptCore.Computational.PqxdhSelectedMessageChecker

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedMessageChecker.hidden_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedMessageChecker.hidden_step
/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedMessageChecker.zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedMessageChecker.zero
/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedMessageChecker.returned_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedMessageChecker.returned_zero
/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedMessageChecker.decision_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedMessageChecker.decision_factor

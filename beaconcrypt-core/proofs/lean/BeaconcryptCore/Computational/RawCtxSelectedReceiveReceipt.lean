import BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord

/-!
Complete receive attribution follows the actual opaque driver through every retained-table derivation before identifying its one reached opening. Rejection remains rejection. A successful known-material opening is distinguished from a selected-material receipt; neither the source getter nor target selection is assumed from an accepted output alone.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedMessageKdf
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedMessageKey
open RawCtxSelectedMessageDriver RawCtxInterpretedReceive
open RawCtxSelectedAuthenticationObserver RawCtxSelectedAcceptedRecord

abbrev Kernel := RawCtxSelectedMessageReveals.Kernel
abbrev Pending := RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Slot RawCtxWholeOwner.OpenContext
abbrev SourceEffect := Effect Slot RawCtxWholeOwner.OpenContext

inductive Terminal where
  | rejected (kernel : Kernel)
  | opening (pending : Pending)

noncomputable def terminal (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (effect : SourceEffect) : Terminal :=
  match effect with
  | .rejected kernel _ => .rejected kernel
  | .openRequested pending => .opening pending
  | .kdfRequested pending => terminal prior parent target nonce next
      (normalResume pending (RawCtxSelectedSendCompiler.deriveValue prior parent target nonce next pending.request))
termination_by effectRank effect
decreasing_by exact normalResume_rank _ _

/-- The actual receive derivation callback evaluates the same complete retained-table routing, including predecessor priority, before the next driver effect. -/
theorem derive_actual (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (request : SymmetricRatchetKdfRequest) :
    RawCtxSelectedReceiveCompiler.compiler prior parent target nonce next read expected (.inl request) =
      pure (RawCtxSelectedSendCompiler.deriveValue prior parent target nonce next request) := by
  simp only [RawCtxSelectedReceiveCompiler.compiler, QueryImpl.compose, receiveCompiler,
    ← QueryImpl.simulateQ_compose]
  exact derive_evaluated prior parent target nonce next request

/-- Every complete cached/future receive is its literal deterministic rejection or its one actual source opening followed by the original finish. -/
theorem program_terminal (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (effect : SourceEffect) :
    simulateQ (RawCtxSelectedReceiveCompiler.compiler prior parent target nonce next read expected)
      (program (Plaintext := RawCtxWholeOwner.Decrypted) effect) =
      match terminal prior parent target nonce next effect with
      | .rejected kernel => pure (kernel, .None)
      | .opening pending => normalFinish pending <$> RawCtxSelectedOpenConsumer.service 0 read expected pending := by
  generalize depth : effectRank effect = rank
  induction rank using Nat.strong_induction_on generalizing effect with
  | h rank ih =>
    cases effect with
    | rejected entry context => simp only [program, terminal, simulateQ_pure]
    | openRequested pending =>
      simp only [program, terminal, simulateQ_map, simulateQ_spec_query,
        RawCtxSelectedReceiveCompiler.compiler, QueryImpl.compose, receiveCompiler,
        RawCtxSelectedReceiveCompiler.service, bind_pure_comp]
    | kdfRequested pending =>
      simp only [program, terminal, simulateQ_bind, simulateQ_spec_query, derive_actual, pure_bind]
      exact ih _ (depth ▸ normalResume_rank pending _) _ rfl

/-- The reached terminal opening has the original target sequence and immutable raw/frame/associated-data context through every actual skipped-key derivation. -/
theorem terminal_scope (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (effect : SourceEffect)
    (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (inScope : RawCtxSelectedReceiveScope.Scope sequence context effect)
    (pending : Pending) (reached : terminal prior parent target nonce next effect = .opening pending) :
    RawCtxInterpretedOpening.sequence pending = ok sequence ∧ pending.context = context := by
  generalize depth : effectRank effect = rank
  induction rank using Nat.strong_induction_on generalizing effect with
  | h rank ih =>
    cases effect with
    | rejected entry actual => simp only [terminal, reduceCtorEq] at reached
    | openRequested actual =>
      simp only [terminal, Terminal.opening.injEq] at reached
      subst pending
      exact inScope
    | kdfRequested request =>
      simp only [terminal] at reached
      exact ih _ (depth ▸ normalResume_rank request _) _
        (by simpa only [inScope.1, inScope.2] using (RawCtxSelectedReceiveScope.resume_scope request
          (RawCtxSelectedSendCompiler.deriveValue prior parent target nonce next request.request))) reached rfl

/-- A successful complete receive reaches an actual opening callback and returns that callback's exact optional plaintext through the original cached/future finish. -/
theorem program_accepts (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (effect : SourceEffect) (before after : State) (kernel : Kernel) (decrypted : RawCtxWholeOwner.Decrypted)
    (supported : ((kernel, .Some decrypted), after) ∈ support (monitor
      (simulateQ (RawCtxSelectedReceiveCompiler.compiler prior parent target nonce next read expected)
        (program (Plaintext := RawCtxWholeOwner.Decrypted) effect)) before)) :
    ∃ pending, terminal prior parent target nonce next effect = .opening pending ∧
      (.Some decrypted, after) ∈ support (monitor (RawCtxSelectedOpenConsumer.service 0 read expected pending) before) ∧
      kernel = (normalFinish pending (.Some decrypted)).1 := by
  rw [program_terminal] at supported
  cases reached : terminal prior parent target nonce next effect with
  | rejected entry =>
    simp only [reached, monitor, simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
      Prod.mk.injEq, reduceCtorEq, and_false, false_and] at supported
  | opening pending =>
    simp only [reached, monitor_map, support_map, Set.mem_image] at supported
    obtain ⟨result, accepted, equal⟩ := supported
    have reply : result.1 = .Some decrypted := congrArg (fun value => value.1.2) equal
    have history : result.2 = after := congrArg Prod.snd equal
    have value : kernel = (normalFinish pending (.Some decrypted)).1 := by
      have same := congrArg (fun value => value.1.1) equal
      simpa only [reply] using same.symm
    refine ⟨pending, rfl, ?_, value⟩
    have same : result = (.Some decrypted, after) := Prod.ext reply history
    rwa [same] at accepted

/-- Acceptance by the actual complete receive discharges the original prepared sequence/context scope rather than assuming an already reached opening. -/
theorem receive_accepts (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (entry : Kernel) (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (before after : State) (kernel : Kernel) (decrypted : RawCtxWholeOwner.Decrypted)
    (supported : ((kernel, .Some decrypted), after) ∈ support (monitor
      (RawCtxSelectedReceiveCompiler.receive prior parent target nonce next read expected entry sequence context) before)) :
    ∃ pending, terminal prior parent target nonce next (normalBegin entry sequence context) = .opening pending ∧
      RawCtxInterpretedOpening.sequence pending = ok sequence ∧ pending.context = context ∧
      (.Some decrypted, after) ∈ support (monitor (RawCtxSelectedOpenConsumer.service 0 read expected pending) before) ∧
      kernel = (normalFinish pending (.Some decrypted)).1 := by
  simp only [RawCtxSelectedReceiveCompiler.receive, RawCtxSelectedMessageDriver.receive,
    ← QueryImpl.simulateQ_compose, RawCtxInterpretedReceive.receive] at supported
  obtain ⟨pending, reached, accepted, finished⟩ := program_accepts prior parent target nonce next read expected
    (normalBegin entry sequence context) before after kernel decrypted supported
  have fields := terminal_scope prior parent target nonce next (normalBegin entry sequence context) sequence context
    (RawCtxSelectedReceiveScope.begin_scope (interpret target) entry sequence context) pending reached
  exact ⟨pending, reached, fields.1, fields.2, accepted, finished⟩

/-- Actual API acceptance supplies the source getter, plaintext, sender and sequence before any selected/known case distinction. -/
theorem service_input (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (pending : Pending) (before after : State) (decrypted : RawCtxWholeOwner.Decrypted)
    (supported : (.Some decrypted, after) ∈ support
      (monitor (RawCtxSelectedOpenConsumer.service slot read expected pending) before)) :
    ∃ (input : RawCtxInterpretedArguments.Input Slot RawCtxWholeOwner.OpenContext) (plaintext : Pqxdh.Bytes),
      RawCtxInterpretedArguments.openArguments pending = some input ∧
      decrypted = ⟨plaintext, input.context.frame.sender, input.sequence⟩ ∧
      (some plaintext, after) ∈ support (monitor (RawCtxUniversalOpening.call slot read expected input) before) := by
  unfold RawCtxSelectedOpenConsumer.service at supported
  cases found : RawCtxInterpretedArguments.openArguments pending with
  | none =>
    simp only [found, monitor, simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
      Prod.mk.injEq, reduceCtorEq, false_and] at supported
  | some input =>
    simp only [found, monitor_map, support_map, Set.mem_image] at supported
    obtain ⟨result, reached, equal⟩ := supported
    cases reply : result.1 with
    | none =>
      have impossible := congrArg (fun value => value.1) equal
      simp only [reply, RawCtxSharedOpeningConsumer.apiReply, reduceCtorEq] at impossible
    | some plaintext =>
      have value : decrypted = ⟨plaintext, input.context.frame.sender, input.sequence⟩ := by
        have same := congrArg Prod.fst equal
        simp only [reply, RawCtxSharedOpeningConsumer.apiReply] at same
        injection same with same
        exact same.symm
      have history : result.2 = after := congrArg Prod.snd equal
      have pair : result = (some plaintext, after) := Prod.ext reply history
      exact ⟨input, plaintext, rfl, value, by rwa [pair] at reached⟩

/-- A successful callback either used actual known material or emitted the exact selected attempted-opening receipt. Byte equality between the two key routes is not excluded. -/
theorem service_branch (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (pending : Pending) (before after : State) (decrypted : RawCtxWholeOwner.Decrypted)
    (supported : (.Some decrypted, after) ∈ support
      (monitor (RawCtxSelectedOpenConsumer.service slot read expected pending) before)) :
    ∃ (input : RawCtxInterpretedArguments.Input Slot RawCtxWholeOwner.OpenContext) (plaintext : Pqxdh.Bytes),
      RawCtxInterpretedArguments.openArguments pending = some input ∧
      decrypted = ⟨plaintext, input.context.frame.sender, input.sequence⟩ ∧
      ((∃ material, input.material = .known material) ∨
        ∃ (nonce : NonceOutput) (width : input.context.associatedData.length = 281),
          input.material = .hidden nonce ∧
          after = step (.inl (.inr (RawCtxUniversalDecoder.pack
            (RawCtxUniversalDecoder.envelope nonce input.context width)))) (some plaintext) before) := by
  obtain ⟨input, plaintext, found, value, reached⟩ := service_input slot read expected pending before after decrypted supported
  refine ⟨input, plaintext, found, value, ?_⟩
  cases material : input.material with
  | known actual => exact Or.inl ⟨actual, rfl⟩
  | hidden nonce =>
    right
    by_cases width : input.context.associatedData.length = 281
    · refine ⟨nonce, width, rfl, ?_⟩
      simp only [RawCtxUniversalOpening.call, material, dite_eq_left width, monitor,
        simulateQ_spec_query, handler, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at reached
      obtain ⟨reply, _, equal⟩ := reached
      have actual : reply = some plaintext := (congrArg Prod.fst equal).symm
      have history := congrArg Prod.snd equal
      simpa only [actual] using history
    · simp only [RawCtxUniversalOpening.call, material, dite_eq_right width, monitor,
        simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at reached

/-- A complete accepted receive retains its original source material getter and either a known-material result or an actual selected receipt. Selecting a hidden slot is not inferred from acceptance. -/
theorem receive_branch (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (entry : Kernel) (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (before after : State) (kernel : Kernel) (decrypted : RawCtxWholeOwner.Decrypted)
    (supported : ((kernel, .Some decrypted), after) ∈ support (monitor
      (RawCtxSelectedReceiveCompiler.receive prior parent target nonce next read expected entry sequence context) before)) :
    ∃ (pending : Pending) (material : Slot) (plaintext : Pqxdh.Bytes),
      terminal prior parent target nonce next (normalBegin entry sequence context) = .opening pending ∧
      RawCtxInterpretedArguments.openArguments pending = some ⟨material, sequence, context⟩ ∧
      decrypted = ⟨plaintext, context.frame.sender, sequence⟩ ∧
      kernel = (normalFinish pending (.Some decrypted)).1 ∧
      ((∃ value, material = .known value) ∨
        ∃ (actualNonce : NonceOutput) (width : context.associatedData.length = 281),
          material = .hidden actualNonce ∧
          after = step (.inl (.inr (RawCtxUniversalDecoder.pack
            (RawCtxUniversalDecoder.envelope actualNonce context width)))) (some plaintext) before) := by
  obtain ⟨pending, reached, prepared, contextSame, accepted, finished⟩ :=
    receive_accepts prior parent target nonce next read expected entry sequence context before after kernel decrypted supported
  obtain ⟨input, plaintext, found, value, branch⟩ := service_branch 0 read expected pending before after decrypted accepted
  obtain ⟨_, inputSequence, inputContext⟩ := RawCtxSelectedOpenConsumer.arguments_some pending input found
  have sequenceSame : input.sequence = sequence := RustM.ok.inj (inputSequence.symm.trans prepared)
  have actualContext : input.context = context := inputContext.trans contextSame
  rcases input with ⟨material, inputSequenceValue, inputContextValue⟩
  dsimp only at sequenceSame actualContext
  subst inputSequenceValue
  subst inputContextValue
  exact ⟨pending, material, plaintext, reached, found, value, finished, branch⟩

/-- Successful raw delivery derives nonempty input, the actual decoder result and source validation from the literal owner prelude, preserving the complete published owner and its incremented attempt counter. -/
theorem raw_accepts {Metadata : Type} (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (owner finalOwner : RawCtxChainOwner.State Kernel Metadata) (before after : State)
    (decrypted : RawCtxWholeOwner.Decrypted)
    (supported : ((.Some decrypted, finalOwner), after) ∈ support (monitor
      (RawCtxSelectedReceiveCompiler.raw prior parent target nonce next read bytes owner) before)) :
    ∃ frame kernel,
      bytes.isEmpty = false ∧ read bytes = some frame ∧
      RawCtxReceive.ValidFrame owner.expectedSender owner.associatedData frame ∧
      ((kernel, .Some decrypted), after) ∈ support (monitor
        (RawCtxSelectedReceiveCompiler.receive prior parent target nonce next read frame.sender
          owner.kernel frame.sequence ⟨bytes, frame, owner.associatedData⟩) before) ∧
      finalOwner = {owner with kernel := kernel, rawAttempts := owner.rawAttempts + 1} := by
  simp only [RawCtxSelectedReceiveCompiler.raw, RawCtxChainOwner.rawReceive, StateT.run] at supported
  by_cases empty : bytes.isEmpty = true
  · simp only [empty, ite_true, monitor, simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
      RawCtxChainOwner.publish, Prod.mk.injEq, reduceCtorEq, false_and] at supported
  · have nonempty : bytes.isEmpty = false := Bool.eq_false_iff.mpr empty
    simp only [empty, Bool.false_eq_true, ite_false] at supported
    cases decoded : read bytes with
    | none =>
      simp only [decoded, monitor, simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
        RawCtxChainOwner.publish, Prod.mk.injEq, reduceCtorEq, false_and] at supported
    | some frame =>
      simp only [decoded] at supported
      by_cases valid : RawCtxReceive.ValidFrame owner.expectedSender owner.associatedData frame
      · simp only [valid, ite_true, bind_pure_comp, monitor_map, support_map, Set.mem_image] at supported
        obtain ⟨result, reached, equal⟩ := supported
        have reply : result.1.2 = .Some decrypted := congrArg (fun value => value.1.1) equal
        have history : result.2 = after := congrArg Prod.snd equal
        have published : finalOwner = {owner with kernel := result.1.1, rawAttempts := owner.rawAttempts + 1} :=
          (congrArg (fun value => value.1.2) equal).symm
        refine ⟨frame, result.1.1, nonempty, rfl, valid, ?_, published⟩
        have same : result = ((result.1.1, .Some decrypted), after) := Prod.ext (Prod.ext rfl reply) history
        rw [same] at reached
        exact reached
      · simp only [valid, ite_false, monitor, simulateQ_pure, StateT.run_pure, mem_support_pure_iff,
          RawCtxChainOwner.publish, Prod.mk.injEq, reduceCtorEq, false_and] at supported

/-- This is an explicit source target event, not a primitive security assumption: the actual complete receive reaches selected material and its full authentication tuple was never successfully sealed before this attempt. -/
def SelectedFresh {Metadata : Type} (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (owner : RawCtxChainOwner.State Kernel Metadata) (before : State) : Prop :=
  ∃ (frame : RawCtxReceive.DecodedFrame) (pending : Pending) (actualNonce : NonceOutput),
    read bytes = some frame ∧
    terminal prior parent target nonce next
      (normalBegin owner.kernel frame.sequence ⟨bytes, frame, owner.associatedData⟩) = .opening pending ∧
    RawCtxInterpretedArguments.openArguments pending =
      some ⟨.hidden actualNonce, frame.sequence, ⟨bytes, frame, owner.associatedData⟩⟩ ∧
    ∀ (width : owner.associatedData.length = 281) (slices : RawCtxFrameDecoding.Slices)
      (parsed : RawCtxFrameDecoding.fromPayload frame.payload = some slices),
      ∀ entry ∈ before.seals, ¬(RawCtxKeyFreeDecoder.target actualNonce frame.sequence frame
        owner.associatedData slices parsed width).toLegacy.sameFullTupleAsSuccessfulSeal entry

/-- Actual raw acceptance on the selected fresh source target produces an ordinary accepted-attempt receipt. The prelude, parsed payload, actual getter, optional plaintext, skipped-key continuation and source publication are all consumed here. -/
theorem raw_selected_record {Metadata : Type} (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (owner finalOwner : RawCtxChainOwner.State Kernel Metadata) (before after : State)
    (decrypted : RawCtxWholeOwner.Decrypted)
    (supported : ((.Some decrypted, finalOwner), after) ∈ support (monitor
      (RawCtxSelectedReceiveCompiler.raw prior parent target nonce next read bytes owner) before))
    (selected : SelectedFresh prior parent target nonce next read bytes owner before) : RecordEvent read after := by
  obtain ⟨frame, kernel, nonempty, decoded, valid, accepted, _⟩ :=
    raw_accepts prior parent target nonce next read bytes owner finalOwner before after decrypted supported
  obtain ⟨pending, reached, _, _, opened, _⟩ := receive_accepts prior parent target nonce next read frame.sender
    owner.kernel frame.sequence ⟨bytes, frame, owner.associatedData⟩ before after kernel decrypted accepted
  obtain ⟨selectedFrame, selectedPending, actualNonce, selectedDecoded, selectedReached, selectedGetter, fresh⟩ := selected
  have frameSame : selectedFrame = frame := Option.some.inj (selectedDecoded.symm.trans decoded)
  subst selectedFrame
  have pendingSame : selectedPending = pending := Terminal.opening.inj (selectedReached.symm.trans reached)
  subst selectedPending
  obtain ⟨slices, parsed⟩ := (RawCtxFrameDecoding.fromPayload_some_iff frame.payload).mpr valid.2.1
  exact selected_service_record 0 read frame.sender pending actualNonce frame.sequence
    ⟨bytes, frame, owner.associatedData⟩ selectedGetter valid.2.2 before nonempty decoded slices parsed
    decrypted after opened (fresh valid.2.2 slices parsed)

/-- The complete raw source event implies the concrete ordinary winner, without evaluating any private-state predicate in the adversary's final decision. -/
theorem raw_selected_wins {Metadata : Type} (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (owner finalOwner : RawCtxChainOwner.State Kernel Metadata) (before after : State)
    (decrypted : RawCtxWholeOwner.Decrypted)
    (supported : ((.Some decrypted, finalOwner), after) ∈ support (monitor
      (RawCtxSelectedReceiveCompiler.raw prior parent target nonce next read bytes owner) before))
    (selected : SelectedFresh prior parent target nonce next read bytes owner before) :
    won (RawCtxUniversalDecoder.decoder read) after = true :=
  record_wins read after (raw_selected_record prior parent target nonce next read bytes owner finalOwner
    before after decrypted supported selected)

/-- Observing the complete arbitrary raw receive adds no queries. Rejected inputs and repeated attempts retain the original one-call component allowance; the separate private derivation allowance remains 51. -/
theorem raw_queries {Metadata : Type} (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (owner : RawCtxChainOwner.State Kernel Metadata) (before : State) :
    (monitor (RawCtxSelectedReceiveCompiler.raw prior parent target nonce next read bytes owner) before).IsTotalQueryBound 1 := by
  have exactBounds := monitor_queries (fun _ => True)
    (RawCtxSelectedReceiveCompiler.raw prior parent target nonce next read bytes owner) before 1
  simp only [IsTotalQueryBound, IsQueryBoundP, not_true_eq_false, false_or, ite_true] at exactBounds ⊢
  exact exactBounds.mpr (RawCtxSelectedReceiveCompiler.raw_queries prior parent target nonce next read bytes owner)

/-- Erasing only receipts recovers the complete actual native raw receive, original owner and shared cache for every input and every optional result. The retained private KDF table and primitive contracts stay explicit. -/
theorem native_raw_erase {A Metadata : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (owner : RawCtxChainOwner.State Kernel Metadata) (state : RawCtxSelectedReceiveCompiler.State A) (before : State) :
    (simulateQ (RawCtxFunctionalFamily.native source writer
        (privateTable prior parent target (response key nonce next)) ∘ₛ RawCtxMixedOwner.receiveAdapter)
      ((RawCtxWholeOwner.rawReceive read bytes).run
        (RawCtxChainOwner.nativeState (RawCtxSelectedMessageReveals.nativeKernel key) owner))).run
          (RawCtxSelectedReceiveCompiler.project state) =
      (fun result => ((result.1.1.1,
        RawCtxChainOwner.nativeState (RawCtxSelectedMessageReveals.nativeKernel key) result.1.1.2),
          RawCtxSelectedReceiveCompiler.project result.2)) <$>
        (RawCtxSelectedReceiveCompiler.evaluated source key read
          (monitor (RawCtxSelectedReceiveCompiler.raw prior parent target nonce next read bytes owner) before)).run state := by
  rw [RawCtxSelectedReceiveCompiler.native_raw]
  have erased := congrArg (fun work => (RawCtxSelectedReceiveCompiler.evaluated source key read work).run state)
    (monitor_erase (RawCtxSelectedReceiveCompiler.raw prior parent target nonce next read bytes owner) before)
  rw [RawCtxSelectedReceiveCompiler.evaluated_map, StateT.run_map] at erased
  rw [← erased]
  simp only [Functor.map_map]

end BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt.derive_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt.derive_actual
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt.program_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt.program_terminal
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt.terminal_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt.terminal_scope
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt.program_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt.program_accepts
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt.receive_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt.receive_accepts
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt.service_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt.service_input
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt.service_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt.service_branch
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt.receive_branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt.receive_branch
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt.raw_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt.raw_accepts
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt.raw_selected_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt.raw_selected_record
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt.raw_selected_wins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt.raw_selected_wins
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt.raw_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt.raw_queries
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt.native_raw_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedReceiveReceipt.native_raw_erase

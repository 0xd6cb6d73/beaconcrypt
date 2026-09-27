import BeaconcryptCore.Computational.LiveRecordEvents

/-!
The actual logged opening callbacks project to decoded protected records while retaining their original raw bytes separately. Every optional callback remains in the private history; only real successful callback plaintexts enter the successful-record projection. Source outer parsing supplies the actual decoder result and selected sequence, including failed opening calls. No unique wire encoding is assumed.

The same supported adaptive source execution supplies its original client result, whole owner/primitive poststate and typed send/raw transcript. Successful callback positions equal successful API receive positions in their actual chronological order. The previously proved source consumption invariant gives no repeated projected position and excludes every position consumed before the continuation, including registration position zero when the actual sequence-one bootstrap has supplied that starting invariant. Positions do not imply distinct material bytes, key independence or cross-owner agreement.

The source specialization retains its fixed functional HKDF, total functional AEAD/shared ROM and optional functional writer interfaces. Its supplied decoder is the existing functional source boundary, not a new proof of a native parser implementation. These source facts do not assume primitive record origin or identify a symbolic strategy/probability law. Whole-frame None callbacks still retain preceding primitive effects; storage, snapshots and restoration are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec BeaconcryptCore.Computational
set_option autoImplicit false
namespace BeaconcryptCore.Computational.LiveDecodedRecordEvents
open LiveRecordEvents

def callPosition : Call → _root_.Option Nat
  | .openFrame input (.Some _) => some (input.sequence.val - 1)
  | _ => none

def openedPositions (history : History) : List Nat := history.filterMap callPosition

def responsePosition (query : LiveOwnerSpec.Domain) : LiveOwnerSpec.Range query → _root_.Option Nat :=
  match query with
  | .inl _ => fun _ => none
  | .inr _ => fun reply => match reply with
      | .None => none
      | .Some message => some (message.sequence.val - 1)

def receivedPositions (transcript : LiveOwnerTranscript) : List Nat :=
  transcript.filterMap (fun request => responsePosition request.1 request.2)

def decodedCall (decode : RawCtxReceive.FrameDecoder) : Call → Prop
  | .seal _ _ => True
  | .openFrame input _ => decode input.context.raw = some input.context.frame ∧
      input.sequence = input.context.frame.sequence

def decodedHistory (decode : RawCtxReceive.FrameDecoder) (history : History) : Prop :=
  ∀ call ∈ history, decodedCall decode call

structure DecodedOpening where
  record : Record
  frame : RawCtxReceive.DecodedFrame

def decodedOpening : Call → _root_.Option DecodedOpening
  | .openFrame input (.Some plaintext) => some ⟨opened input plaintext, input.context.frame⟩
  | _ => none

def decodedOpenings (history : History) : List DecodedOpening := history.filterMap decodedOpening

/-- A real logged callback contributes exactly the successful API position, preserving every rejected and send branch. -/
theorem worker_step_positions {AD PT CT Metadata PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (sealing : RawCtxSourceSend.SealInput → StateT PrimitiveState (OracleComp base) (_root_.Option Pqxdh.Bytes))
    (opening : RawCtxWholeOwner.OpenInput → StateT PrimitiveState (OracleComp base) (core.option.Option Pqxdh.Bytes))
    (decode : RawCtxReceive.FrameDecoder)
    {initial final : LiveOwnerConfiguration Metadata (PrimitiveState × History)}
    {query : LiveOwnerSpec.Domain} {reply : LiveOwnerSpec.Range query}
    (step : LiveOwnerStep cr (loggedSeal sealing) (loggedOpen opening) decode initial query reply final) :
    openedPositions final.2.2 = openedPositions initial.2.2 ++ (responsePosition query reply).toList := by
  cases step with
  | rejectSend => simp [responsePosition]
  | rejectRaw => simp [responsePosition]
  | send token after attempts primitive post plaintext reply nonempty core =>
      cases core with
      | rejectSend => simp [responsePosition]
      | send token primitive context reply after called =>
          simp only [liveOwnerSealing] at called
          split at called
          · simp_all [openedPositions, responsePosition]
          · simp only [StateT.run_bind, mem_support_bind_iff, StateT.run_pure, support_pure, Set.mem_singleton_iff] at called
            obtain ⟨result, called, equal⟩ := called
            rw [logged_seal_support] at called
            obtain ⟨callback, primitiveAfter, actual, rfl⟩ := called
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
            simp [openedPositions, callPosition, responsePosition]
  | raw token after attempts primitive post raw frame reply nonempty decoded valid core =>
      cases core with
      | rejectReceive => simp [responsePosition]
      | receive token primitive target context material committed reply after prepared called =>
          simp only [liveOwnerOpening, live_word_source] at called
          simp only [StateT.run_bind, mem_support_bind_iff, StateT.run_pure, support_pure, Set.mem_singleton_iff] at called
          obtain ⟨result, called, equal⟩ := called
          rw [logged_open_support] at called
          obtain ⟨callback, primitiveAfter, actual, rfl⟩ := called
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
          cases callback <;> simp [openedPositions, callPosition, responsePosition, RawCtxOwnerResult.mapReply, RawCtxWholeOwner.decrypted]
/-- Every reached opening, including None, keeps the original outer decoder result and the same selected frame sequence. -/
theorem worker_step_decoded {AD PT CT Metadata PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (sealing : RawCtxSourceSend.SealInput → StateT PrimitiveState (OracleComp base) (_root_.Option Pqxdh.Bytes))
    (opening : RawCtxWholeOwner.OpenInput → StateT PrimitiveState (OracleComp base) (core.option.Option Pqxdh.Bytes))
    (decode : RawCtxReceive.FrameDecoder)
    {initial final : LiveOwnerConfiguration Metadata (PrimitiveState × History)}
    {query : LiveOwnerSpec.Domain} {reply : LiveOwnerSpec.Range query}
    (prior : decodedHistory decode initial.2.2)
    (step : LiveOwnerStep cr (loggedSeal sealing) (loggedOpen opening) decode initial query reply final) :
    decodedHistory decode final.2.2 := by
  cases step with
  | rejectSend => exact prior
  | rejectRaw => exact prior
  | send token after attempts primitive post plaintext reply nonempty core =>
      cases core with
      | rejectSend => exact prior
      | send token primitive context reply after called =>
          simp only [liveOwnerSealing] at called
          split at called
          · simp_all [decodedHistory]
          · simp only [StateT.run_bind, mem_support_bind_iff, StateT.run_pure, support_pure, Set.mem_singleton_iff] at called
            obtain ⟨result, called, equal⟩ := called
            rw [logged_seal_support] at called
            obtain ⟨callback, primitiveAfter, actual, rfl⟩ := called
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
            simpa [decodedHistory, decodedCall, or_imp, forall_and] using prior
  | raw token after attempts primitive post raw frame reply nonempty decoded valid core =>
      cases core with
      | rejectReceive => exact prior
      | receive token primitive target context material committed reply after prepared called =>
          simp only [liveOwnerOpening, live_word_source] at called
          simp only [StateT.run_bind, mem_support_bind_iff, StateT.run_pure, support_pure, Set.mem_singleton_iff] at called
          obtain ⟨result, called, equal⟩ := called
          rw [logged_open_support] at called
          obtain ⟨callback, primitiveAfter, actual, rfl⟩ := called
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
          simpa [decodedHistory, decodedCall, liveRawContext, decoded, or_imp, forall_and] using prior
/-- The complete serial worker trace preserves the exact chronological callback-to-API position list. -/
theorem worker_trace_positions {AD PT CT Metadata PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (sealing : RawCtxSourceSend.SealInput → StateT PrimitiveState (OracleComp base) (_root_.Option Pqxdh.Bytes))
    (opening : RawCtxWholeOwner.OpenInput → StateT PrimitiveState (OracleComp base) (core.option.Option Pqxdh.Bytes))
    (decode : RawCtxReceive.FrameDecoder)
    {initial final : LiveOwnerConfiguration Metadata (PrimitiveState × History)}
    {transcript : LiveOwnerTranscript}
    (trace : LiveOwnerTrace cr (loggedSeal sealing) (loggedOpen opening) decode initial transcript final) :
    openedPositions final.2.2 = openedPositions initial.2.2 ++ receivedPositions transcript := by
  induction trace with
  | nil state => simp [receivedPositions]
  | @step state next final query reply rest actual tail ih =>
      rw [ih, worker_step_positions cr sealing opening decode actual]
      cases choice : responsePosition query reply <;> simp [receivedPositions, choice, List.append_assoc]

/-- The same trace preserves raw-buffer and decoded-frame provenance for every opening callback. -/
theorem worker_trace_decoded {AD PT CT Metadata PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (sealing : RawCtxSourceSend.SealInput → StateT PrimitiveState (OracleComp base) (_root_.Option Pqxdh.Bytes))
    (opening : RawCtxWholeOwner.OpenInput → StateT PrimitiveState (OracleComp base) (core.option.Option Pqxdh.Bytes))
    (decode : RawCtxReceive.FrameDecoder)
    {initial final : LiveOwnerConfiguration Metadata (PrimitiveState × History)}
    {transcript : LiveOwnerTranscript}
    (prior : decodedHistory decode initial.2.2)
    (trace : LiveOwnerTrace cr (loggedSeal sealing) (loggedOpen opening) decode initial transcript final) :
    decodedHistory decode final.2.2 := by
  induction trace with
  | nil state => exact prior
  | @step state next final query reply rest actual tail ih =>
      exact ih (worker_step_decoded cr sealing opening decode prior actual)

/-- The existing prepend-style source monitor is exactly the reverse chronological successful receive list followed by prior consumed positions. -/
theorem spent_positions (transcript : LiveOwnerTranscript) (spent : List Nat) :
    spentAfter transcript spent = (receivedPositions transcript).reverse ++ spent := by
  induction transcript generalizing spent with
  | nil => rfl
  | cons request rest ih =>
      rw [spentAfter, ih]
      rcases request with ⟨query, reply⟩
      cases query with
      | inl plaintext => simp [receivedPositions, responsePosition, RawCtxReceiveConsumption.recordSource]
      | inr raw =>
          cases reply <;> simp [receivedPositions, responsePosition, RawCtxReceiveConsumption.recordSource, RawCtxReceiveConsumption.recordReply, List.append_assoc]

/-- Source-derived consumption uniqueness transfers to successful callback positions on the same trace. -/
theorem worker_opened_nodup {AD PT CT Metadata PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (sealing : RawCtxSourceSend.SealInput → StateT PrimitiveState (OracleComp base) (_root_.Option Pqxdh.Bytes))
    (opening : RawCtxWholeOwner.OpenInput → StateT PrimitiveState (OracleComp base) (core.option.Option Pqxdh.Bytes))
    (decode : RawCtxReceive.FrameDecoder)
    {initial final : LiveOwnerConfiguration Metadata (PrimitiveState × History)}
    {transcript : LiveOwnerTranscript} (spent : List Nat)
    (trace : LiveOwnerTrace cr (loggedSeal sealing) (loggedOpen opening) decode initial transcript final)
    (empty : initial.2.2 = []) (unique : (spentAfter transcript spent).Nodup) :
    (openedPositions final.2.2).Nodup := by
  rw [worker_trace_positions cr sealing opening decode trace, empty]
  rw [spent_positions] at unique
  simpa [openedPositions] using List.nodup_reverse.mp unique.of_append_left

/-- A projected record identifies its actual logged material/context/plaintext and original successfully decoded frame, without raw encoding injectivity. -/
theorem decoded_openings_provenance (decode : RawCtxReceive.FrameDecoder) (history : History)
    (wellFormed : decodedHistory decode history)
    (observation : DecodedOpening) (present : observation ∈ decodedOpenings history) :
    ∃ input plaintext,
      Call.openFrame input (.Some plaintext) ∈ history ∧
      observation = ⟨opened input plaintext, input.context.frame⟩ ∧
      decode observation.record.raw = some observation.frame ∧
      observation.record.sequence = observation.frame.sequence ∧
      observation.record.sender = observation.frame.sender := by
  obtain ⟨call, member, mapped⟩ := List.mem_filterMap.mp present
  cases call with
  | «seal» input reply => simp [decodedOpening] at mapped
  | openFrame input reply =>
      cases reply with
      | none => simp [decodedOpening] at mapped
      | some plaintext =>
          simp only [decodedOpening, _root_.Option.some.injEq] at mapped
          refine ⟨input, plaintext, member, mapped.symm, ?_⟩
          simpa [← mapped, opened, decodedCall] using wellFormed _ member

/-- Decoded successful-record positions are precisely the successful callback position projection. -/
theorem decoded_openings_positions (history : History) :
    (decodedOpenings history).map (fun observation => observation.record.sequence.val - 1) =
      openedPositions history := by
  induction history with
  | nil => rfl
  | cons call rest ih =>
      cases call with
      | «seal» input reply =>
          change (decodedOpenings rest).map (fun observation => observation.record.sequence.val - 1) =
            openedPositions rest
          exact ih
      | openFrame input reply =>
          cases reply with
          | none =>
              change (decodedOpenings rest).map (fun observation => observation.record.sequence.val - 1) =
                openedPositions rest
              exact ih
          | some plaintext =>
              change (input.sequence.val - 1) ::
                  (decodedOpenings rest).map (fun observation => observation.record.sequence.val - 1) =
                (input.sequence.val - 1) :: openedPositions rest
              exact congrArg (List.cons (input.sequence.val - 1)) ih

/-- The same source consumption history excludes every position consumed before this continuation. -/
theorem worker_opened_fresh {AD PT CT Metadata PrimitiveState ι : Type} {base : OracleSpec ι}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (sealing : RawCtxSourceSend.SealInput → StateT PrimitiveState (OracleComp base) (_root_.Option Pqxdh.Bytes))
    (opening : RawCtxWholeOwner.OpenInput → StateT PrimitiveState (OracleComp base) (core.option.Option Pqxdh.Bytes))
    (decode : RawCtxReceive.FrameDecoder)
    {initial final : LiveOwnerConfiguration Metadata (PrimitiveState × History)}
    {transcript : LiveOwnerTranscript} (spent : List Nat)
    (trace : LiveOwnerTrace cr (loggedSeal sealing) (loggedOpen opening) decode initial transcript final)
    (empty : initial.2.2 = []) (unique : (spentAfter transcript spent).Nodup) :
    ∀ position ∈ openedPositions final.2.2, position ∉ spent := by
  rw [worker_trace_positions cr sealing opening decode trace, empty]
  rw [spent_positions] at unique
  intro position present previous
  exact (List.nodup_append.mp unique).2.2 position (by simpa [openedPositions] using present)
    position previous rfl

/-- One actual supported source result retains original transcript/state, decoded record provenance and nonrepeating positions disjoint from its prior consumed history. -/
theorem source_supported_decoded_records {AD PT CT Metadata Auxiliary Result : Type}
    (cr : Ratchet.Crypto RatchetChain RatchetMaterial AD PT CT)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sendOrigin receiveOrigin : RatchetChain) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp LiveOwnerSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary)
    (token : LiveToken (LiveOwnerContext Metadata)) (represented : LiveOwnerRepresents sender state.1 token)
    (spent : List Nat)
    (invariant : RawCtxReceiveConsumption.ConsumedRefines source.crypto sendOrigin receiveOrigin state.1.owner.kernel spent)
    (result : Result × (RawCtxWholeOwner.OwnerState Metadata × RawCtxSharedPrimitive.SharedState Auxiliary))
    (actual : result ∈ support ((simulateQ (RawCtxMixedOwner.sourceImpl
      (RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source)) sender decode) client).run state)) :
    ∃ history transcript,
      (result.1, (result.2.1, (result.2.2, history))) ∈ support
        ((simulateQ (liveOwnerSourceImpl (RawCtxSourceHkdf.response source.crypto)
          (loggedSeal (sourceSealing source writer)) (loggedOpen (sourceOpening source writer)) sender decode)
          client).run (state.1, (state.2, []))) ∧
      LiveOwnerSourceTrace (RawCtxSourceHkdf.response source.crypto)
        (sourceSealing source writer) (sourceOpening source writer) sender decode state transcript result.2 ∧
      decodedHistory decode history ∧ openedPositions history = receivedPositions transcript ∧
      ((decodedOpenings history).map (fun observation => observation.record.sequence.val - 1)).Nodup ∧
      (∀ position ∈ openedPositions history, position ∉ spent) := by
  obtain ⟨history, transcript, after, monitored, original, representedAfter, live, consumed, unique⟩ :=
    source_supported_consumption cr source writer sendOrigin receiveOrigin sender decode
      client state token represented spent invariant result actual
  refine ⟨history, transcript, monitored, original, ?_, ?_, ?_, ?_⟩
  · exact worker_trace_decoded (withInterpreter cr (RawCtxSourceHkdf.response source.crypto))
      (sourceSealing source writer) (sourceOpening source writer) decode (by simp [decodedHistory]) live
  · simpa [openedPositions] using worker_trace_positions
      (withInterpreter cr (RawCtxSourceHkdf.response source.crypto))
      (sourceSealing source writer) (sourceOpening source writer) decode live
  · rw [decoded_openings_positions]
    exact worker_opened_nodup (withInterpreter cr (RawCtxSourceHkdf.response source.crypto))
      (sourceSealing source writer) (sourceOpening source writer) decode spent live rfl unique
  · exact worker_opened_fresh (withInterpreter cr (RawCtxSourceHkdf.response source.crypto))
      (sourceSealing source writer) (sourceOpening source writer) decode spent live rfl unique

end BeaconcryptCore.Computational.LiveDecodedRecordEvents

/--
info: 'BeaconcryptCore.Computational.LiveDecodedRecordEvents.worker_step_positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveDecodedRecordEvents.worker_step_positions

/--
info: 'BeaconcryptCore.Computational.LiveDecodedRecordEvents.worker_step_decoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveDecodedRecordEvents.worker_step_decoded

/--
info: 'BeaconcryptCore.Computational.LiveDecodedRecordEvents.worker_trace_positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveDecodedRecordEvents.worker_trace_positions

/--
info: 'BeaconcryptCore.Computational.LiveDecodedRecordEvents.worker_trace_decoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveDecodedRecordEvents.worker_trace_decoded

/--
info: 'BeaconcryptCore.Computational.LiveDecodedRecordEvents.spent_positions' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveDecodedRecordEvents.spent_positions

/--
info: 'BeaconcryptCore.Computational.LiveDecodedRecordEvents.worker_opened_nodup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveDecodedRecordEvents.worker_opened_nodup

/--
info: 'BeaconcryptCore.Computational.LiveDecodedRecordEvents.decoded_openings_provenance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveDecodedRecordEvents.decoded_openings_provenance

/--
info: 'BeaconcryptCore.Computational.LiveDecodedRecordEvents.decoded_openings_positions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveDecodedRecordEvents.decoded_openings_positions

/--
info: 'BeaconcryptCore.Computational.LiveDecodedRecordEvents.worker_opened_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveDecodedRecordEvents.worker_opened_fresh

/--
info: 'BeaconcryptCore.Computational.LiveDecodedRecordEvents.source_supported_decoded_records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveDecodedRecordEvents.source_supported_decoded_records

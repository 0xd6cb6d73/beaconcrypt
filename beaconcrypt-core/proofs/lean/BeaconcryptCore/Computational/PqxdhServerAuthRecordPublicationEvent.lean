import BeaconcryptCore.Computational.PqxdhServerAuthPublication
import BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl

/-! A public decoded-record observation for initial registration. Optional writer readback is an explicit abstract message contract, never writer totality or an implementation proof. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationEvent
open PqxdhServerAuthExperiment PqxdhServerAuthPublicationOccurrence
variable {Reader Response : Type}

/-- Parse only public response bytes and their optional inner record, using the actual abstract message functions. -/
def frame (codec : Codec Reader Response) (raw : Pqxdh.Bytes) : Option RawCtxReceive.DecodedFrame := do
  let response ← codec.read2 raw
  let application ← codec.application response
  codec.frameRead application

/-- The original raw request is retained only when this exact public finish returned success. -/
def finishRaw : ((query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) → Option Pqxdh.Bytes
  | ⟨.inr (.finish raw), some _⟩ => some raw
  | _ => none

/-- Public raw bytes at the first successful finish; later calls cannot select another acceptance. -/
def acceptedRaw (journal : QueryLog ServerAuthSpec) : Option Pqxdh.Bytes :=
  journal.findSome? finishRaw

/-- A concrete earlier successful build at this source coordinate returns the same decoded record as the actual accepted public raw request. It asserts neither byte-canonical encoding nor full cryptographic-session equality. -/
def RecordPublished (codec : Codec Reader Response) (index : Nat) (journal : QueryLog ServerAuthSpec) : Prop :=
  ∃ payload reply raw record,
    (⟨.inr (.build index payload), some reply⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈
      beforeAcceptance journal ∧
    acceptedRaw journal = some raw ∧ frame codec raw = some record ∧ frame codec reply.serialized = some record

/-- The terminal observation uses only the actual chronological public journal and fixed source coordinate. -/
noncomputable def observer (codec : Codec Reader Response) (index : Nat) : PqxdhServerAuthObservedEntry.Observer :=
  fun _ journal => @decide (¬ RecordPublished codec index journal) (Classical.propDecidable _)

/-- Existing one-way message readback laws recover the actual successfully written frame. Neither writer is required to succeed on any other input. -/
theorem frame_written (codec : Codec Reader Response)
    (responseBack : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (fields : PqxdhServerRegistrationPublication.ResponseFields) (raw : Pqxdh.Bytes)
    (record : RawCtxReceive.DecodedFrame)
    (outer : codec.write2 fields = some raw)
    (inner : codec.frameWrite record = some fields.appCiphertext) : frame codec raw = some record := by
  obtain ⟨response, read, _, _, _, _, application⟩ := responseBack fields raw outer
  simpa only [frame, read, Option.bind_eq_bind, Option.bind_some, application] using (frameBack record fields.appCiphertext inner).2

/-- The public raw selector and the existing success-prefix test inspect the same optional reply. -/
theorem finishRaw_none (event : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) :
    finishRaw event = none ↔ finishReturned event = false := by
  rcases event with ⟨coin | query, reply⟩
  · simp only [finishRaw, finishReturned]
  · cases query <;> simp only [finishRaw, finishReturned, iff_self]
    cases reply <;> simp

/-- The public selector chooses the literal successful finish after an arbitrary rejected prefix, regardless of later calls. -/
theorem accepted_before_finish (before after : QueryLog ServerAuthSpec) (raw payload : Pqxdh.Bytes)
    (prior : ∀ event ∈ before, finishReturned event = false) :
    acceptedRaw (before ++ ⟨.inr (.finish raw), some payload⟩ :: after) = some raw := by
  have empty : before.findSome? finishRaw = none := List.findSome?_eq_none_iff.mpr
    (fun event member => (finishRaw_none event).mpr (prior event member))
  simp only [acceptedRaw, List.findSome?_append, empty, List.findSome?_cons, finishRaw, Option.or]

/-- Record publication implies a successful earlier outer publication at the same source occurrence; no codec law is needed in this direction. -/
theorem record_published (codec : Codec Reader Response) (index : Nat) (journal : QueryLog ServerAuthSpec)
    (published : RecordPublished codec index journal) : Published index journal := by
  obtain ⟨payload, reply, raw, record, earlier, _⟩ := published
  exact ⟨payload, reply, earlier⟩

/-- The final public decision exposes exactly the missing decoded-record event. -/
theorem observer_true (codec : Codec Reader Response) (index : Nat) (ghost : Ghost) (journal : QueryLog ServerAuthSpec) :
    observer codec index ghost journal = true ↔ ¬ RecordPublished codec index journal := by
  simp only [observer, decide_eq_true_eq]

/-- Actual successful inner/outer writer arguments and the accepted decoded record produce the exact public event. Source occurrence and chronology remain explicit receipt obligations. -/
theorem receipt_event (codec : Codec Reader Response)
    (responseBack : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (frameBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (index : Nat) (journal : QueryLog ServerAuthSpec) (payload : Option Pqxdh.Bytes)
    (reply : PqxdhServerRegistrationPublication.Response) (raw : Pqxdh.Bytes)
    (record : RawCtxReceive.DecodedFrame) (fields : PqxdhServerRegistrationPublication.ResponseFields)
    (earlier : (⟨.inr (.build index payload), some reply⟩ :
      (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) ∈ beforeAcceptance journal)
    (accepted : acceptedRaw journal = some raw) (decoded : frame codec raw = some record)
    (outer : codec.write2 fields = some reply.serialized)
    (inner : codec.frameWrite record = some fields.appCiphertext) : RecordPublished codec index journal := by
  exact ⟨payload, reply, raw, record, earlier, accepted, decoded,
    frame_written codec responseBack frameBack fields reply.serialized record outer inner⟩

end BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationEvent

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationEvent.frame_written' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationEvent.frame_written

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationEvent.finishRaw_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationEvent.finishRaw_none

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationEvent.accepted_before_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationEvent.accepted_before_finish

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationEvent.record_published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationEvent.record_published

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationEvent.observer_true' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationEvent.observer_true

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationEvent.receipt_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRecordPublicationEvent.receipt_event

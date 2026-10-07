-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler

/-! The actual local source execution transports installation coordinates through both directions, skips, cached consumption and failed-opening rollback. Coordinate origins are private annotations, never inferred from key bytes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates
open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable PqxdhRecordLiftMaterialTable PqxdhRecordLiftChainCompiler
variable {Slot Context Plaintext PrimitiveState : Type}

/-- A receive keeps the send coordinate and advances only the original receive coordinate, at most 51 source derivations. -/
def ReceiveCoordinates (entry after : LabeledKernel Slot) : Prop :=
  after.send_chain = entry.send_chain ∧
    ∃ count, count ≤ 51 ∧ after.receive_chain = advance entry.receive_chain count

/-- Actual cached/future publication, including a failed opening, preserves the original private coordinate origins. -/
theorem finish_coordinates (entry : LabeledKernel Slot) (context : Context) (target : Std.U64)
    (pending : RawCtxInterpretedOpening.Opening (Label Slot) (Label Slot) (Label Slot) Context)
    (tracked : Tracked entry context (.openRequested pending))
    (admitted : PqxdhFirstRecordReplay.Admitted entry target (.openRequested pending))
    (reply : core.option.Option Plaintext) :
    ReceiveCoordinates entry (RawCtxChainReceive.normalFinish pending reply).1 := by
  cases reply with
  | none =>
      rw [failed_open entry context pending tracked]
      exact ⟨rfl, 0, by omega, by simp [advance]⟩
  | some plaintext =>
      have prepared : PqxdhFirstRecordReplay.Prepared pending.entry target pending.prepared := by
        simpa only [admitted.1] using admitted.2
      have run := RawCtxChainReceive.normalFinish_exact pending (.Some plaintext)
      generalize RawCtxChainReceive.normalFinish pending (.Some plaintext) = result at run ⊢
      cases shape : pending.prepared with
      | PreparedReceiveCachedCase cached =>
          rw [shape] at prepared
          obtain ⟨out, executed, _, send, recv, _⟩ := publish_cached_receive_exact pending.entry cached
            prepared.target_bound prepared.last_bound
          simp only [RawCtxInterpretedOpening.finish, shape, executed, bind_tc_ok, RustM.ok.injEq] at run
          cases run
          exact ⟨send.trans (congrArg RefinedRatchet.send_chain tracked.1),
            0, by omega, by simpa only [advance, Nat.add_zero, tracked.1] using recv⟩
      | PreparedReceiveFutureCase future =>
          rw [shape] at prepared
          obtain ⟨_, first, _, _, capacity, cached⟩ := prepared
          have length := congrArg List.length cached
          simp only [control.cacheSeqs_length, List.length_append, List.length_map, List.length_range] at length
          have bounded : future.first_slot.val + future.skipped.val ≤ 50 := by
            simp only [control.RatchetState.Wf, control.SequenceCache.Wf] at capacity
            rw [first]
            omega
          obtain ⟨out, executed, _, send, recv, _⟩ := publish_future_receive_exact pending.entry future bounded
          simp only [RawCtxInterpretedOpening.finish, shape, executed, bind_tc_ok, RustM.ok.injEq] at run
          cases run
          refine ⟨send.trans (congrArg RefinedRatchet.send_chain tracked.1), future.skipped.val + 1, by omega, ?_⟩
          exact recv.trans (by simpa only [Tracked, shape] using tracked.2.2)

/-- The complete actual recursive receive retains its installation coordinates under arbitrary native replies and table work. -/
theorem receive_coordinates (seeds : Seeds Slot) (lookup : Lookup Slot PrimitiveState)
    (opening : Open Context Plaintext PrimitiveState) (entry : LabeledKernel Slot) (context : Context) (target : Std.U64)
    (effect : Effect Slot Context) (tracked : Tracked entry context effect)
    (admitted : PqxdhFirstRecordReplay.Admitted entry target effect)
    (state : Execution Slot PrimitiveState)
    (result : (LabeledKernel Slot × core.option.Option Plaintext) × Execution Slot PrimitiveState)
    (supported : result ∈ support ((receive seeds lookup opening effect).run state)) :
    ReceiveCoordinates entry result.1.1 := by
  generalize hdepth : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect state result with
  | h depth ih =>
    cases effect with
    | rejected original prior =>
      simp only [StateT.run, receive, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨congrArg RefinedRatchet.send_chain tracked.1, 0, by omega,
        by simpa only [advance, Nat.add_zero] using congrArg RefinedRatchet.receive_chain tracked.1⟩
    | openRequested pending =>
      simp only [StateT.run, receive, bind_pure_comp, support_map] at supported
      obtain ⟨reply, _, equal⟩ := supported
      subst result
      exact finish_coordinates entry context target pending tracked admitted reply.1
    | kdfRequested pending =>
      simp only [StateT.run, receive, mem_support_bind_iff] at supported
      obtain ⟨reply, _, continued⟩ := supported
      exact ih _ (hdepth ▸ RawCtxChainReceive.normalResume_rank pending (advance pending.request 1, pending.request))
        _ (resume_tracked entry context pending pending.request tracked)
        (PqxdhFirstRecordReplay.resume_admitted entry target pending (advance pending.request 1, pending.request) admitted)
        reply.2 result continued rfl

/-- Source admission supplies the provenance premises for every target sequence; no chosen execution trace is assumed. -/
theorem admitted_receive_coordinates (seeds : Seeds Slot) (lookup : Lookup Slot PrimitiveState)
    (opening : Open Context Plaintext PrimitiveState) (entry : LabeledKernel Slot) (context : Context) (target : Std.U64)
    (capacity : entry.control.Wf) (state : Execution Slot PrimitiveState)
    (result : (LabeledKernel Slot × core.option.Option Plaintext) × Execution Slot PrimitiveState)
    (supported : result ∈ support ((receive seeds lookup opening
      (RawCtxChainReceive.normalBegin entry target context)).run state)) :
    ReceiveCoordinates entry result.1.1 :=
  receive_coordinates seeds lookup opening entry context target _ (begin_tracked entry context target)
    (PqxdhFirstRecordReplay.begin_admitted entry target context capacity) state result supported

/-- Exact coordinate advancement preserves both slot and direction, including a failed-opening retry. -/
theorem receive_origins (entry after : LabeledKernel Slot) (tracked : ReceiveCoordinates entry after) :
    after.send_chain = entry.send_chain ∧ after.receive_chain.slot = entry.receive_chain.slot ∧
      after.receive_chain.direction = entry.receive_chain.direction := by
  obtain ⟨send, count, _, recv⟩ := tracked
  exact ⟨send, by simp only [recv, advance], by simp only [recv, advance]⟩

/-- A source send changes only its own coordinate, by zero on exhaustion or one before sealing, and preserves the complete receive cache. -/
def SendCoordinates (entry after : LabeledKernel Slot) : Prop :=
  after.receive_chain = entry.receive_chain ∧ after.receive_slots = entry.receive_slots ∧
    ∃ count, count ≤ 1 ∧ after.send_chain = advance entry.send_chain count

/-- Complete send execution preserves provenance even if the native seal/writer returns no ciphertext. -/
theorem send_coordinates {Output : Type} (seeds : Seeds Slot) (lookup : Lookup Slot PrimitiveState)
    (sealing : Seal Context Output PrimitiveState) (entry : LabeledKernel Slot) (context : Context)
    (start : Start Slot Context) (tracked : SendTracked entry context start) (state : Execution Slot PrimitiveState)
    (result : (LabeledKernel Slot × Option Output) × Execution Slot PrimitiveState)
    (supported : result ∈ support ((send seeds lookup sealing start).run state)) :
    SendCoordinates entry result.1.1 := by
  cases start with
  | exhausted original prior =>
      simp only [StateT.run, send, support_pure, Set.mem_singleton_iff] at supported
      subst result
      rw [tracked.1]
      exact ⟨rfl, rfl, 0, by omega, by simp [advance]⟩
  | requested pending =>
      simp only [StateT.run, send, mem_support_bind_iff] at supported
      obtain ⟨reply, _, sealed, _, equal⟩ := supported
      simp only [support_pure, Set.mem_singleton_iff] at equal
      subst result
      rw [send_ready_kernel entry context pending pending.request tracked]
      exact ⟨rfl, rfl, 1, le_rfl, rfl⟩

/-- Actual source send admission supplies all provenance premises, including the exhausted-counter path. -/
theorem admitted_send_coordinates {Output : Type} (seeds : Seeds Slot) (lookup : Lookup Slot PrimitiveState)
    (sealing : Seal Context Output PrimitiveState) (entry : LabeledKernel Slot) (context : Context)
    (state : Execution Slot PrimitiveState)
    (result : (LabeledKernel Slot × Option Output) × Execution Slot PrimitiveState)
    (supported : result ∈ support ((send seeds lookup sealing (RawCtxChainSend.normalBegin entry context)).run state)) :
    SendCoordinates entry result.1.1 :=
  send_coordinates seeds lookup sealing entry context _ (send_begin_tracked entry context) state result supported

/-- Both send origins and the unchanged opposite-direction cache retain their installed slot and direction. -/
theorem send_origins (entry after : LabeledKernel Slot) (tracked : SendCoordinates entry after) :
    after.receive_chain = entry.receive_chain ∧ after.receive_slots = entry.receive_slots ∧
      after.send_chain.slot = entry.send_chain.slot ∧ after.send_chain.direction = entry.send_chain.direction := by
  obtain ⟨recv, slots, count, _, sent⟩ := tracked
  exact ⟨recv, slots, by simp only [sent, advance], by simp only [sent, advance]⟩

/-- Future opening validation retains the original send counter; cached counters follow the existing source preparation facts. -/
def FutureSendAligned : Effect Slot Context → Prop
  | .openRequested pending => match pending.prepared with
    | .PreparedReceiveFutureCase future => future.committed_control.send_sequence = pending.entry.control.send_sequence
    | .PreparedReceiveCachedCase _ => True
  | _ => True

/-- The actual source validator checks the opposite-direction counter before producing a future opening. -/
theorem resume_future_send (pending : RawCtxChainReceive.Kdf (Label Slot) (Label Slot) (Label Slot) Context) :
    FutureSendAligned (RawCtxChainReceive.normalResume pending (advance pending.request 1, pending.request)) := by
  have run := RawCtxChainReceive.normalResume_exact pending (advance pending.request 1, pending.request)
  generalize RawCtxChainReceive.normalResume pending (advance pending.request 1, pending.request) = effect at run ⊢
  unfold RawCtxChainReceive.resume at run
  repeat' first | (obtain ⟨_, _, run⟩ := PqxdhFirstRecordReplay.rust_bind_ok run) | split at run
  all_goals cases RustM.ok.inj run
  all_goals first | trivial | skip
  simp only [FutureSendAligned]
  by_contra different
  rename_i _ _ _ _ _ _ _ _ _ _ _ checked accepted _ _ _
  rw [accepted] at checked
  simp [pending_receive_is_valid, control.RatchetState.impl.receive_sequence,
    control.RatchetState.impl.send_sequence, control.RatchetState.receive_cache_len, different] at checked

/-- Admission emits no future opening before a checked source derivation. -/
theorem begin_future_send (entry : LabeledKernel Slot) (target : Std.U64) (context : Context) :
    FutureSendAligned (RawCtxChainReceive.normalBegin entry target context) := by
  have run := RawCtxChainReceive.normalBegin_exact entry target context
  generalize RawCtxChainReceive.normalBegin entry target context = effect at run ⊢
  unfold RawCtxChainReceive.beginReceive at run
  repeat' first | (obtain ⟨_, _, run⟩ := PqxdhFirstRecordReplay.rust_bind_ok run) | split at run
  all_goals cases RustM.ok.inj run
  all_goals trivial

/-- Cached consumption, successful future publication and complete rollback all preserve both source counter coordinates. -/
theorem finish_aligned (entry : LabeledKernel Slot) (context : Context) (target : Std.U64)
    (pending : RawCtxInterpretedOpening.Opening (Label Slot) (Label Slot) (Label Slot) Context)
    (aligned : Aligned entry) (capacity : entry.control.Wf)
    (tracked : Tracked entry context (.openRequested pending))
    (admitted : PqxdhFirstRecordReplay.Admitted entry target (.openRequested pending))
    (sender : FutureSendAligned (.openRequested pending)) (reply : core.option.Option Plaintext) :
    Aligned (RawCtxChainReceive.normalFinish pending reply).1 := by
  cases reply with
  | none => simpa only [failed_open entry context pending tracked] using aligned
  | some plaintext =>
      have prepared : PqxdhFirstRecordReplay.Prepared pending.entry target pending.prepared := by
        simpa only [admitted.1] using admitted.2
      have entryAligned : Aligned pending.entry := by simpa only [tracked.1] using aligned
      have entryCapacity : pending.entry.control.Wf := by simpa only [tracked.1] using capacity
      have run := RawCtxChainReceive.normalFinish_exact pending (.Some plaintext)
      generalize RawCtxChainReceive.normalFinish pending (.Some plaintext) = result at run ⊢
      cases shape : pending.prepared with
      | PreparedReceiveCachedCase cached =>
          rw [shape] at prepared
          obtain ⟨finished, finishedEq, _, _, sendCounter, recvCounter, _⟩ :=
            control.finish_receive_consumed pending.entry.control target cached.target_slot entryCapacity
              prepared.target_live prepared.entry
          have controlEq := congrArg control.ReceiveFinishWithRemoval.state (RustM.ok.inj (finishedEq.symm.trans prepared.finish))
          rw [controlEq] at sendCounter recvCounter
          change cached.committed_control.send_sequence = pending.entry.control.send_sequence at sendCounter
          change cached.committed_control.receive_sequence = pending.entry.control.receive_sequence at recvCounter
          obtain ⟨out, executed, controlEq, send, recv, _⟩ := publish_cached_receive_exact pending.entry cached
            prepared.target_bound prepared.last_bound
          simp only [RawCtxInterpretedOpening.finish, shape, executed, bind_tc_ok, RustM.ok.injEq] at run
          cases run
          simpa only [Aligned, send, recv, controlEq, sendCounter, recvCounter] using entryAligned
      | PreparedReceiveFutureCase future =>
          rw [shape] at prepared
          have recvAligned := future_sequence pending.entry pending.context target future entryAligned
            ⟨rfl, rfl, by simpa only [tracked.1, shape] using tracked.2.2⟩ prepared
          have sendCounter : future.committed_control.send_sequence = pending.entry.control.send_sequence := by
            simpa only [FutureSendAligned, shape] using sender
          obtain ⟨_, first, _, _, capacity, cached⟩ := prepared
          have length := congrArg List.length cached
          simp only [control.cacheSeqs_length, List.length_append, List.length_map, List.length_range] at length
          have bounded : future.first_slot.val + future.skipped.val ≤ 50 := by
            simp only [control.RatchetState.Wf, control.SequenceCache.Wf] at capacity
            rw [first]
            omega
          obtain ⟨out, executed, controlEq, send, recv, _⟩ := publish_future_receive_exact pending.entry future bounded
          simp only [RawCtxInterpretedOpening.finish, shape, executed, bind_tc_ok, RustM.ok.injEq] at run
          cases run
          exact ⟨by simpa only [send, controlEq, sendCounter] using entryAligned.1,
            by simpa only [recv, controlEq] using recvAligned⟩

/-- Every actual recursive receive keeps both counters aligned and every retained skipped material attributed to its original source coordinate. -/
theorem receive_invariants (seeds : Seeds Slot) (lookup : Lookup Slot PrimitiveState)
    (opening : Open Context Plaintext PrimitiveState) (entry : LabeledKernel Slot) (context : Context) (target : Std.U64)
    (aligned : Aligned entry) (capacity : entry.control.Wf) (effect : Effect Slot Context)
    (tracked : Tracked entry context effect) (admitted : PqxdhFirstRecordReplay.Admitted entry target effect)
    (sender : FutureSendAligned effect) (attributed : EffectAttributed entry.receive_chain effect)
    (state : Execution Slot PrimitiveState)
    (result : (LabeledKernel Slot × core.option.Option Plaintext) × Execution Slot PrimitiveState)
    (supported : result ∈ support ((receive seeds lookup opening effect).run state)) :
    Aligned result.1.1 ∧ SlotsAttributed entry.receive_chain result.1.1.receive_slots := by
  generalize hdepth : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect state result with
  | h depth ih =>
    cases effect with
    | rejected original prior =>
      simp only [StateT.run, receive, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨by simpa only [tracked.1] using aligned, attributed⟩
    | openRequested pending =>
      simp only [StateT.run, receive, bind_pure_comp, support_map] at supported
      obtain ⟨reply, _, equal⟩ := supported
      subst result
      refine ⟨finish_aligned entry context target pending aligned capacity tracked admitted sender reply.1, ?_⟩
      apply finish_property (Attributed entry.receive_chain) pending target
        (by simpa only [admitted.1] using admitted.2) attributed.1
      cases shape : pending.prepared with
      | PreparedReceiveCachedCase cached => trivial
      | PreparedReceiveFutureCase future =>
          simp only [EffectAttributed, shape] at attributed
          exact attributed.2.1
    | kdfRequested pending =>
      simp only [StateT.run, receive, mem_support_bind_iff] at supported
      obtain ⟨reply, _, continued⟩ := supported
      exact ih _ (hdepth ▸ RawCtxChainReceive.normalResume_rank pending (advance pending.request 1, pending.request))
        _ (resume_tracked entry context pending pending.request tracked)
        (PqxdhFirstRecordReplay.resume_admitted entry target pending (advance pending.request 1, pending.request) admitted)
        (resume_future_send pending)
        (resume_source_attributed entry context target pending aligned tracked admitted attributed.1 attributed.2)
        reply.2 result continued rfl

/-- Cache attribution depends on the installed slot and direction, while each cached material retains its own earlier position. -/
theorem attributed_reanchor (before after : Label Slot) (slot : after.slot = before.slot)
    (direction : after.direction = before.direction) (slots : Slots Slot) :
    SlotsAttributed after slots ↔ SlotsAttributed before slots := by
  simp only [SlotsAttributed, Attributed, slot, direction]

/-- Actual source admission and complete receive execution preserve counter alignment and all skipped-key coordinate tags. -/
theorem admitted_receive_invariants (seeds : Seeds Slot) (lookup : Lookup Slot PrimitiveState)
    (opening : Open Context Plaintext PrimitiveState) (entry : LabeledKernel Slot) (context : Context) (target : Std.U64)
    (aligned : Aligned entry) (capacity : entry.control.Wf)
    (attributed : SlotsAttributed entry.receive_chain entry.receive_slots) (state : Execution Slot PrimitiveState)
    (result : (LabeledKernel Slot × core.option.Option Plaintext) × Execution Slot PrimitiveState)
    (supported : result ∈ support ((receive seeds lookup opening
      (RawCtxChainReceive.normalBegin entry target context)).run state)) :
    Aligned result.1.1 ∧ SlotsAttributed result.1.1.receive_chain result.1.1.receive_slots := by
  have facts := receive_invariants seeds lookup opening entry context target aligned capacity _
    (begin_tracked entry context target) (PqxdhFirstRecordReplay.begin_admitted entry target context capacity)
    (begin_future_send entry target context) (begin_attributed entry.receive_chain entry attributed target context)
    state result supported
  have origins := receive_origins entry result.1.1
    (admitted_receive_coordinates seeds lookup opening entry context target capacity state result supported)
  exact ⟨facts.1, (attributed_reanchor entry.receive_chain result.1.1.receive_chain origins.2.1 origins.2.2 _).mpr facts.2⟩

/-- Source sends preserve aligned positions and all receive-cache attribution, even when sealing returns no ciphertext. -/
theorem send_invariants {Output : Type} (seeds : Seeds Slot) (lookup : Lookup Slot PrimitiveState)
    (sealing : Seal Context Output PrimitiveState) (entry : LabeledKernel Slot) (context : Context)
    (aligned : Aligned entry) (attributed : SlotsAttributed entry.receive_chain entry.receive_slots)
    (start : Start Slot Context) (tracked : SendTracked entry context start) (state : Execution Slot PrimitiveState)
    (result : (LabeledKernel Slot × Option Output) × Execution Slot PrimitiveState)
    (supported : result ∈ support ((send seeds lookup sealing start).run state)) :
    Aligned result.1.1 ∧ SlotsAttributed result.1.1.receive_chain result.1.1.receive_slots := by
  have coordinates := send_coordinates seeds lookup sealing entry context start tracked state result supported
  refine ⟨?_, by simpa only [coordinates.1, coordinates.2.1] using attributed⟩
  cases start with
  | exhausted original prior =>
      simp only [StateT.run, send, support_pure, Set.mem_singleton_iff] at supported
      subst result
      simpa only [tracked.1] using aligned
  | requested pending =>
      simp only [StateT.run, send, mem_support_bind_iff] at supported
      obtain ⟨reply, _, sealed, _, equal⟩ := supported
      simp only [support_pure, Set.mem_singleton_iff] at equal
      subst result
      exact send_ready_aligned entry context pending pending.request aligned tracked

/-- The actual source send entry establishes the tracked premises automatically. -/
theorem admitted_send_invariants {Output : Type} (seeds : Seeds Slot) (lookup : Lookup Slot PrimitiveState)
    (sealing : Seal Context Output PrimitiveState) (entry : LabeledKernel Slot) (context : Context)
    (aligned : Aligned entry) (attributed : SlotsAttributed entry.receive_chain entry.receive_slots)
    (state : Execution Slot PrimitiveState)
    (result : (LabeledKernel Slot × Option Output) × Execution Slot PrimitiveState)
    (supported : result ∈ support ((send seeds lookup sealing (RawCtxChainSend.normalBegin entry context)).run state)) :
    Aligned result.1.1 ∧ SlotsAttributed result.1.1.receive_chain result.1.1.receive_slots :=
  send_invariants seeds lookup sealing entry context aligned attributed _ (send_begin_tracked entry context) state result supported

/-- Local source reachability certificate: valid replay/cache control, exact counter positions and actual skipped-material coordinates. -/
def Certified (kernel : LabeledKernel Slot) : Prop :=
  control.ValidControl kernel.control ∧ Aligned kernel ∧ SlotsAttributed kernel.receive_chain kernel.receive_slots

/-- Every raw receive's local source execution preserves the certificate, including rejected attempts and successful cache consumption. -/
theorem receive_certified (seeds : Seeds Slot) (lookup : Lookup Slot PrimitiveState)
    (opening : Open Context Plaintext PrimitiveState) (entry : LabeledKernel Slot) (context : Context) (target : Std.U64)
    (certified : Certified entry) (state : Execution Slot PrimitiveState)
    (result : (LabeledKernel Slot × core.option.Option Plaintext) × Execution Slot PrimitiveState)
    (supported : result ∈ support ((receive seeds lookup opening
      (RawCtxChainReceive.normalBegin entry target context)).run state)) : Certified result.1.1 := by
  refine ⟨?_, admitted_receive_invariants seeds lookup opening entry context target certified.2.1
    certified.1.capacity certified.2.2 state result supported⟩
  have facts := receive_control seeds lookup opening entry target certified.1 _
    (PqxdhFirstRecordReplay.begin_admitted entry target context certified.1.capacity) state result supported
  cases response : result.1.2 with
  | none => simpa only [facts.1 response] using certified.1
  | some plaintext => exact (facts.2 plaintext response).1

/-- Source send advancement changes no receive-control fact; the exhausted path retains the complete certificate. -/
theorem send_certified {Output : Type} (seeds : Seeds Slot) (lookup : Lookup Slot PrimitiveState)
    (sealing : Seal Context Output PrimitiveState) (entry : LabeledKernel Slot) (context : Context)
    (certified : Certified entry) (state : Execution Slot PrimitiveState)
    (result : (LabeledKernel Slot × Option Output) × Execution Slot PrimitiveState)
    (supported : result ∈ support ((send seeds lookup sealing (RawCtxChainSend.normalBegin entry context)).run state)) :
    Certified result.1.1 := by
  refine ⟨?_, admitted_send_invariants seeds lookup sealing entry context certified.2.1 certified.2.2 state result supported⟩
  have tracked := send_begin_tracked entry context
  generalize RawCtxChainSend.normalBegin entry context = start at tracked supported
  cases start with
  | exhausted original prior =>
      simp only [StateT.run, send, support_pure, Set.mem_singleton_iff] at supported
      subst result
      simpa only [tracked.1] using certified.1
  | requested pending =>
      simp only [StateT.run, send, mem_support_bind_iff] at supported
      obtain ⟨reply, _, sealed, _, equal⟩ := supported
      simp only [support_pure, Set.mem_singleton_iff] at equal
      subst result
      rw [send_ready_kernel entry context pending pending.request tracked]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [control.RatchetState.Wf, tracked.2.2.2.2.2] using certified.1.capacity
      · simpa only [tracked.2.2.2.2.2] using certified.1.positive
      · simpa only [tracked.2.2.2.2.2, tracked.2.2.2.2.1] using certified.1.past
      · simpa only [tracked.2.2.2.2.2] using certified.1.unique

/-- Both actual post-registration seed constructors establish the local certificate in the correct opposite role orientations. -/
theorem seeds_certified (slot : Slot) :
    (∃ kernel, PqxdhRecordLiftMaterialTable.serverLabels slot = ok kernel ∧ Certified kernel) ∧
      (∃ kernel, PqxdhRecordLiftMaterialTable.beaconLabels slot = ok kernel ∧ Certified kernel) := by
  obtain ⟨⟨server, serverEq, serverAligned, _, _, serverSlots⟩,
    ⟨beacon, beaconEq, beaconAligned, _, _, beaconSlots⟩⟩ :=
    PqxdhRecordLiftMaterialTable.seeds_certified (∅ : Table Slot) slot
  refine ⟨⟨server, serverEq, ?_, serverAligned, serverSlots⟩,
    ⟨beacon, beaconEq, ?_, beaconAligned, beaconSlots⟩⟩
  · obtain ⟨built, builtEq, valid, _⟩ := refined.from_counters_valid (Material := Label Slot)
      1#u64 0#u64 (⟨slot, false, 1⟩ : Label Slot) (⟨slot, true, 0⟩ : Label Slot)
    cases RustM.ok.inj (builtEq.symm.trans serverEq)
    exact valid.control
  · obtain ⟨built, builtEq, valid, _⟩ := refined.from_counters_valid (Material := Label Slot)
      0#u64 1#u64 (⟨slot, true, 0⟩ : Label Slot) (⟨slot, false, 1⟩ : Label Slot)
    cases RustM.ok.inj (builtEq.symm.trans beaconEq)
    exact valid.control

end BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.finish_coordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.finish_coordinates

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.receive_coordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.receive_coordinates

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.admitted_receive_coordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.admitted_receive_coordinates

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.receive_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.receive_origins

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.send_coordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.send_coordinates

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.admitted_send_coordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.admitted_send_coordinates

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.send_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.send_origins

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.resume_future_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.resume_future_send

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.begin_future_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.begin_future_send

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.finish_aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.finish_aligned

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.receive_invariants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.receive_invariants

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.attributed_reanchor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.attributed_reanchor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.admitted_receive_invariants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.admitted_receive_invariants

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.send_invariants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.send_invariants

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.admitted_send_invariants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.admitted_send_invariants

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.receive_certified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.receive_certified

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.send_certified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.send_certified

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.seeds_certified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates.seeds_certified

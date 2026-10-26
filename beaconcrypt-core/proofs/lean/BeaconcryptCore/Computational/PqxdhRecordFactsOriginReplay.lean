-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftFlat

/-! Exact replay witnesses used by the record origin argument. The source frame is recovered from the checked record parser and the full record context, including sequence and sender. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginReplay
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxReplayDictionary
open PqxdhRecordLiftIdeal

/-- A successful replay reply has an actual dictionary entry with the same nonce, full record context and encoded record. -/
theorem replay_witness (state : CtxIndependentTags.CtxIndependentTagState)
    (target : CtxUnclaimedAcceptance.Target) (plaintext : Pqxdh.Bytes)
    (accepted : replayPlaintext state target = some plaintext) :
    ∃ entry ∈ state.successfulSeals,
      target.nonce = entry.input.nonce ∧ target.context.ad = entry.input.context.ad ∧
      target.record.encode = entry.record.encode ∧ entry.input.plaintext = plaintext := by
  obtain ⟨entry, located, value⟩ := Option.map_eq_some_iff.mp accepted
  have same := List.find?_some located
  exact ⟨entry, List.mem_of_find?_eq_some located,
    (of_decide_eq_true same).1, (of_decide_eq_true same).2.1, (of_decide_eq_true same).2.2, value⟩

/-- Normalizing an accepted payload retains every payload byte. -/
theorem normalized_record (frame : RawCtxReceive.DecodedFrame)
    (slices : RawCtxFrameDecoding.Slices)
    (parsed : RawCtxFrameDecoding.fromPayload frame.payload = some slices) :
    (RawCtxKeyFreeDecoder.record frame slices parsed).encode = frame.payload := by
  exact (RawCtxFrameDecoding.fromPayload_record frame.payload slices parsed).choose_spec.2.2.2.2.2.2.2

/-- The decoded frame fields carried by a replay-dictionary seal. -/
def Matches (frame : RawCtxReceive.DecodedFrame) (entry : CtxSuccessfulSeal) : Prop :=
  frame.sequence.val = entry.input.context.ad.seq ∧
    frame.sender.val = entry.input.context.ad.sid ∧ frame.payload = entry.record.encode

/-- The full context fixes the outer sequence and sender as well as every protected payload byte. -/
theorem target_matches (nonce : CtxNonce) (frame : RawCtxReceive.DecodedFrame)
    (ad : Pqxdh.Bytes) (slices : RawCtxFrameDecoding.Slices)
    (parsed : RawCtxFrameDecoding.fromPayload frame.payload = some slices)
    (width : ad.length = 281) (entry : CtxSuccessfulSeal)
    (same : (RawCtxKeyFreeDecoder.target nonce frame.sequence frame ad slices parsed width).toLegacy.sameFullTupleAsSuccessfulSeal entry) :
    Matches frame entry := by
  exact ⟨congrArg Pqxdh.RecordAD.seq same.2.1,
    congrArg Pqxdh.RecordAD.sid same.2.1, (normalized_record frame slices parsed).symm.trans same.2.2⟩

/-- Matching a source-generated seal yields equality of its complete decoded frame. -/
theorem matches_selected (frame : RawCtxReceive.DecodedFrame) (nonce : CtxNonce)
    (sequence : Std.U64) (context : RawCtxSourceSend.SealContext)
    (width : context.associatedData.length = 281) (record : CtxRomRecord)
    (same : Matches frame ⟨RawCtxSelectedMessageSealing.selectedInput nonce sequence context width, record⟩) :
    frame = ⟨sequence, context.senderId, record.encode⟩ := by
  have sequenceEq : frame.sequence = sequence := UScalar.eq_of_val_eq same.1
  have senderEq : frame.sender = context.senderId := UScalar.eq_of_val_eq same.2.1
  cases frame; simp_all only [Matches, RawCtxSelectedMessageSealing.selectedInput]

/-- Private cache access preserves the complete seal dictionary, including cache hits before the first seal. -/
theorem localPrivate_seals (suffix : Pqxdh.Bytes) (before : KeyEntry)
    (result : CtxDigest × KeyEntry)
    (supported : result ∈ support (AdaptiveCtxSharedReplay.localPrivate suffix before)) :
    result.2.1.successfulSeals = before.1.successfulSeals := by
  simp only [AdaptiveCtxSharedReplay.localPrivate, bind_pure_comp, support_map] at supported
  obtain ⟨_, _, rfl⟩ := supported; rfl

/-- Every accepted raw replay returns the dictionary's optional plaintext unchanged. -/
theorem localRaw_accepted (decode : RawDecoder) (raw : Pqxdh.Bytes) (before : KeyEntry)
    (plaintext : Pqxdh.Bytes) (after : KeyEntry)
    (supported : (some plaintext, after) ∈ support (AdaptiveCtxSharedReplay.localRaw decode raw before)) :
    ∃ target, decode raw = some target ∧
      replayPlaintext (AdaptiveCtxSharedReplay.install before ∅).ctx target = some plaintext ∧
      after.1.successfulSeals = before.1.successfulSeals := by
  unfold AdaptiveCtxSharedReplay.localRaw at supported
  cases decoded : decode raw <;> simp only [decoded, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
    Option.some_ne_none, false_and, bind_pure_comp, support_map, Option.some.injEq, exists_eq_left' ] at supported ⊢
  obtain ⟨result, reached, equal⟩ := supported
  exact ⟨congrArg Prod.fst equal,
    (congrArg (fun state : KeyEntry => state.1.successfulSeals) (congrArg Prod.snd equal)).symm.trans
      (localPrivate_seals _ ({ before.1 with rawAttempts := before.1.rawAttempts + 1 }, before.2) result reached)⟩

/-- In replay and random modes, acceptance is exactly a previous full-tuple dictionary match. -/
theorem keyRaw_witness (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (mode : KeyMode) (ideal : mode ≠ .real) (raw : Pqxdh.Bytes) (before : KeyEntry)
    (plaintext : Pqxdh.Bytes) (after : KeyEntry)
    (supported : (some plaintext, after) ∈ support ((keyImpl decode crypto key mode (.inr raw)).run before)) :
    ∃ target, decode raw = some target ∧ ∃ entry ∈ before.1.successfulSeals,
      target.nonce = entry.input.nonce ∧ target.context.ad = entry.input.context.ad ∧
      target.record.encode = entry.record.encode ∧ entry.input.plaintext = plaintext := by
  have replay : (some plaintext, after) ∈ support (AdaptiveCtxSharedReplay.localRaw decode raw before) := by
    cases mode <;> first | exact False.elim (ideal rfl) | exact supported
  exact (localRaw_accepted decode raw before plaintext after replay).elim fun target facts =>
    ⟨target, facts.1, replay_witness (AdaptiveCtxSharedReplay.install before ∅).ctx target plaintext facts.2.1⟩

/-- A successful universal decode refers to the actual raw frame and its parsed payload. -/
theorem decoder_frame (read : RawCtxReceive.FrameDecoder) (envelope : RawCtxUniversalDecoder.Envelope)
    (target : CtxUnclaimedAcceptance.Target)
    (decoded : RawCtxUniversalDecoder.decoder read (RawCtxUniversalDecoder.pack envelope) = some target) :
    ∃ frame, read envelope.raw = some frame ∧ ∃ slices, ∃
      (parsed : RawCtxFrameDecoding.fromPayload frame.payload = some slices),
      target = RawCtxKeyFreeDecoder.target envelope.nonce frame.sequence frame envelope.ad.toList slices parsed envelope.ad.2 := by
  simp only [RawCtxUniversalDecoder.decoder, RawCtxUniversalDecoder.unpack_pack,
    Option.bind_eq_bind, Option.bind_some] at decoded
  split at decoded <;> try contradiction
  cases readFrame : read envelope.raw <;> simp only [readFrame, RawCtxUniversalDecoder.decodeFrame] at decoded <;> try contradiction
  split at decoded <;> try contradiction
  exact ⟨_, rfl, _, by assumption, (Option.some.inj decoded).symm⟩

/-- An accepted framed raw opening in either ideal mode has a source-frame witness and its exact dictionary plaintext. -/
theorem keyRaw_frame (read : RawCtxReceive.FrameDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (mode : KeyMode) (ideal : mode ≠ .real) (envelope : RawCtxUniversalDecoder.Envelope)
    (before : KeyEntry) (plaintext : Pqxdh.Bytes) (after : KeyEntry)
    (supported : (some plaintext, after) ∈ support
      ((keyImpl (RawCtxUniversalDecoder.decoder read) crypto key mode
        (.inr (RawCtxUniversalDecoder.pack envelope))).run before)) :
    ∃ frame, read envelope.raw = some frame ∧ ∃ entry ∈ before.1.successfulSeals,
      Matches frame entry ∧ entry.input.plaintext = plaintext := by
  obtain ⟨target, decoded, entry, member, nonce, context, record, value⟩ :=
    keyRaw_witness (RawCtxUniversalDecoder.decoder read) crypto key mode ideal _ before plaintext after supported
  obtain ⟨frame, readFrame, slices, parsed, rfl⟩ := decoder_frame read envelope target decoded
  exact ⟨frame, readFrame, entry, member,
    target_matches envelope.nonce frame envelope.ad.toList slices parsed envelope.ad.2 entry
      ⟨nonce, context, record⟩, value⟩

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginReplay

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReplay.replay_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReplay.replay_witness

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReplay.normalized_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReplay.normalized_record

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReplay.target_matches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReplay.target_matches

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReplay.matches_selected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReplay.matches_selected

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReplay.localPrivate_seals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReplay.localPrivate_seals

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReplay.localRaw_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReplay.localRaw_accepted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReplay.keyRaw_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReplay.keyRaw_witness

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReplay.decoder_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReplay.decoder_frame

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginReplay.keyRaw_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginReplay.keyRaw_frame

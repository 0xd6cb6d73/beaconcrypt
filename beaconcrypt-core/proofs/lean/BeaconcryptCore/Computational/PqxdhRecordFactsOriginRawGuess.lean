-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMuteUntilBad
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginReplay

/-! Selected replay matches expose a digest candidate from the original raw input only. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawGuess
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate)
open PqxdhRecordFactsOriginMuteUntilBad
variable {n : Nat}

/-- Equal complete encoded records have identical full commitment fields. -/
theorem encoded_commit (left right : CtxRomRecord) (same : left.encode = right.encode) :
    left.commit = right.commit := by
  have decoded := congrArg Pqxdh.decodeRecord same
  simp only [decodeRecord_romRecord, Option.some.injEq] at decoded
  exact List.Vector.toList_injective (congrArg Pqxdh.RecordCipher.commit decoded)

/-- Extract only the public commitment from the original raw bytes, retaining empty, frame and payload rejection. -/
noncomputable def candidate (read : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) : Option CtxDigest :=
  if raw.isEmpty then none else
  match read raw with
  | none => none
  | some frame =>
      match parsed : RawCtxFrameDecoding.fromPayload frame.payload with
      | none => none
      | some slices => some (RawCtxKeyFreeDecoder.record frame slices parsed).commit

/-- The private nonce/AD envelope does not affect the raw commitment candidate. -/
theorem candidate_pack (read : RawCtxReceive.FrameDecoder) (envelope : RawCtxUniversalDecoder.Envelope) :
    (RawCtxUniversalDecoder.decoder read (RawCtxUniversalDecoder.pack envelope)).map
      (fun target => target.record.commit) = candidate read envelope.raw := by
  simp only [RawCtxUniversalDecoder.decoder, RawCtxUniversalDecoder.unpack_pack,
    Option.bind_eq_bind, Option.bind_some, candidate]
  split
  · rfl
  · cases read envelope.raw with
    | none => rfl
    | some frame =>
        simp only [RawCtxUniversalDecoder.decodeFrame]
        split <;> split <;> simp_all [RawCtxKeyFreeDecoder.target]
        congr 2
        grind


/-- A selected replay flag supplies a literal dictionary member whose commitment is in the actual decoded input. -/
theorem raw_bad (target : Label n) (decode : RawDecoder) (label : Label n)
    (bytes : Pqxdh.Bytes) (state : CtxPrivate n)
    (hit : rawBad target decode label bytes state = true) :
    ∃ entry ∈ (state.keys target).1.successfulSeals,
      (decode bytes).map (fun parsed => parsed.record.commit) = some entry.record.commit := by
  simp only [rawBad] at hit
  split at hit
  · rename_i same
    subst label
    cases parsed : decode bytes <;> simp only [PqxdhRecordFactsHashLocal.keyedRawResult,
      PqxdhRecordFactsHashLocal.rawResult, parsed, Option.isSome_none, Bool.false_eq_true] at hit
    obtain ⟨plaintext, accepted⟩ := Option.isSome_iff_exists.mp hit
    obtain ⟨entry, member, _, _, same, _⟩ := PqxdhRecordFactsOriginReplay.replay_witness _ _ plaintext accepted
    exact ⟨entry, member, congrArg some (encoded_commit _ _ same)⟩
  · contradiction


/-- An actual selected opening flag yields the digest candidate from the unchanged raw network bytes. -/
theorem opening_bad (target : Label n) (read : RawCtxReceive.FrameDecoder)
    (pending : PqxdhRecordLiftProtocol.Opening n) (state : CtxPrivate n)
    (hit : openingBad target (RawCtxUniversalDecoder.decoder read) pending state = true) :
    ∃ entry ∈ (state.keys target).1.successfulSeals,
      candidate read pending.context.raw = some entry.record.commit := by
  unfold openingBad at hit
  split at hit
  · contradiction
  · split at hit
    · contradiction
    · rename_i input arguments
      split at hit
      · obtain ⟨entry, member, same⟩ := raw_bad target (RawCtxUniversalDecoder.decoder read) _ _ state hit
        have contextEq : input.context = pending.context :=
          (PqxdhRecordLiftCtxHybrid.openArguments_facts _ input arguments).2
        exact ⟨entry, member, by simpa only [candidate_pack, RawCtxUniversalDecoder.envelope, contextEq] using same⟩
      · contradiction


/-- One public digest candidate per literal hidden opening request; other source services contribute none. -/
noncomputable def serviceCandidate (read : RawCtxReceive.FrameDecoder)
    (query : PqxdhRecordLiftProtocol.Service n) : Option CtxDigest :=
  match query with
  | .opening pending => candidate read pending.context.raw
  | _ => none

/-- Every selected service flag yields a dictionary commitment in that request's public raw candidate. -/
theorem service_bad (target : Label n) (read : RawCtxReceive.FrameDecoder)
    (query : PqxdhRecordLiftProtocol.Service n) (state : CtxPrivate n)
    (hit : serviceBad target (RawCtxUniversalDecoder.decoder read) query state = true) :
    ∃ entry ∈ (state.keys target).1.successfulSeals,
      serviceCandidate read query = some entry.record.commit := by
  cases query <;> simp only [serviceBad, Bool.false_eq_true] at hit
  exact opening_bad target read _ state hit


/-- Every retained candidate consumes the existing raw-service bill, including malformed or unsuccessful opening replies. -/
theorem service_candidate_counted (read : RawCtxReceive.FrameDecoder)
    (query : PqxdhRecordLiftProtocol.Service n) (digest : CtxDigest)
    (present : serviceCandidate read query = some digest) :
    PqxdhRecordLiftCtxProtocolBounds.categoryCost .raw query = 1 := by
  cases query <;> simp_all [serviceCandidate, PqxdhRecordLiftCtxProtocolBounds.categoryCost]


/-- If the retained selected dictionary carries one fixed digest, a raised flag is an actual public raw-input guess of that digest. -/
theorem service_bad_guess (target : Label n) (read : RawCtxReceive.FrameDecoder)
    (query : PqxdhRecordLiftProtocol.Service n) (state : CtxPrivate n) (digest : CtxDigest)
    (fixed : ∀ entry ∈ (state.keys target).1.successfulSeals, entry.record.commit = digest)
    (hit : serviceBad target (RawCtxUniversalDecoder.decoder read) query state = true) :
    serviceCandidate read query = some digest := by
  obtain ⟨entry, member, same⟩ := service_bad target read query state hit
  exact same.trans (congrArg some (fixed entry member))

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawGuess

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawGuess.encoded_commit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawGuess.encoded_commit
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawGuess.candidate_pack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawGuess.candidate_pack
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawGuess.raw_bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawGuess.raw_bad
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawGuess.opening_bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawGuess.opening_bad
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawGuess.service_bad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawGuess.service_bad
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawGuess.service_candidate_counted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawGuess.service_candidate_counted
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawGuess.service_bad_guess' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginRawGuess.service_bad_guess

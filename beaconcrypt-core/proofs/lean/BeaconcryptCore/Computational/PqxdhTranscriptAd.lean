-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CtxRomAuth
import BeaconcryptCore.Model.Pqxdh.SessionTranscript
import BeaconcryptCore.Refinement.SessionTranscript
import BeaconcryptCore.Refinement.TranscriptAuthInputs
import BeaconcryptCore.Computational.PqxdhEd25519EufCma
import BeaconcryptCore.Computational.PqxdhBeaconPhase2Preparation
import BeaconcryptCore.Computational.PqxdhJointPhase1SourceWriter
import BeaconcryptCore.Computational.PqxdhJointPhase1Reports

/-!
# Registration v3 associated data from the transcript hash (pure layer)

Both honest roles compute the record associated data per session as `AD151 = context87 ‖ BLAKE2b-512(T2638)`, where `T2638 = Pqxdh.SessionTranscript.encode init response` is built from the four retained signed Init buffers exactly as written or received (Ed25519 signatures included) and the four response fields available before sealing (Server identity key, ephemeral key, KEM ciphertext, assigned key ID). This module holds the pure part of that computation for the generic model; it imports no experiment (the experiment imports it) and has no section variable.

- Fields and preimage. `initOf` reads the four Init buffers of a Phase-1 candidate; `adResponse` and `serverResponse` read the four response fields (through the refinement's `absResponse`); `transcript` is the exact 2638-byte preimage with no tag and no length; `query` is the one unkeyed BLAKE2b-512 request of the shared lazy random oracle `CtxRomAuth.ctxRandomOracle` (the same oracle that answers the adversary's hash queries and every CTX commitment).
- Assembly. `digestBytes` turns a 64-byte oracle digest into an extracted array, `adOf` assembles context87 followed by it, and `completedOf` is the generic completed binding the Beacon stage receives: its `associated_data` is `adOf digest` (`completedOf_ad`). Its Server ML-DSA key and request hash are fixed all-zero placeholders (`unmodeledPinKey`, `unmodeledInitHash`): the generic model has neither, and the generic Beacon layer never reads them.
- Refinement. `adOf_exact` (the extracted `assemble_associated_data` returns `adOf`), `adOf_bytes`, `digestBytes_abs`, and `transcript_extracted` (the extracted `build_record_ad_transcript` returns the model preimage on exact-width inputs).
- Leaves. `query_eq_of_ad_eq`, `transcript_eq_of_ad_eq`: outside a cache collision (VCVio `CacheHasCollision`), equal assembled AD of two cached digests gives equal queries, hence equal transcripts. `identityKey_eq_of_transcript_eq`, `identity_of_transcript_eq`: equal transcripts give equal 33-byte identity buffers, so the identity a Server verified is the identity an honest Beacon wrote. `fields_of_transcript_eq` recovers all fields under the four width facts, which `accept_wellFormed`/`verified_wellFormed` supply for an accepted candidate.

No assumption is used: hashing stays the lazily sampled random oracle; the collision event is an explicit hypothesis whose probability is bounded elsewhere.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM PqxdhRefinement beaconcrypt_core

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhTranscriptAd
open Pqxdh.SessionTranscript

/-- The registration v3 record associated data: context87 followed by the 64-byte transcript digest. -/
abbrev AssociatedData := Std.Array Std.U8 151#usize

/-- The four retained Init buffers exactly as written or received, Ed25519 signatures included. -/
def initOf (candidate : PqxdhEd25519EufCma.Phase1Candidate) : InitFields :=
  ⟨candidate.identityKey, candidate.preKey, candidate.oneTimeKey, candidate.pqKey⟩

/-- The four response fields available before sealing. -/
def adResponse (identity ephemeral : PqxdhBeaconPhase2Preparation.Word32)
    (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext) (keyId : Std.U64) : ResponseFields :=
  SessionTranscriptRefinement.absResponse ⟨identity, ephemeral, ciphertext, keyId⟩

/-- The response fields of a Server registration candidate. -/
def serverResponse (candidate : pqxdh.ServerRegistrationCandidate) : ResponseFields :=
  adResponse candidate.server_identity_public_key candidate.ephemeral_public_key candidate.kem_ciphertext
    candidate.key_id

/-- The exact 2638-byte preimage (no tag, no length). -/
def transcript (init : InitFields) (response : ResponseFields) : Pqxdh.Bytes := encode init response

/-- The one unkeyed BLAKE2b-512 query of the shared oracle. -/
def query (init : InitFields) (response : ResponseFields) : CtxRomAuth.CtxRO.Domain :=
  ((), transcript init response)

/-- A 64-byte oracle digest as an extracted byte array. -/
def digestBytes (digest : CtxRomAuth.CtxDigest) : Std.Array Std.U8 64#usize :=
  ⟨digest.toList.map fun byte => ⟨byte.toBitVec⟩, by simp⟩

/-- The assembled associated data: context87 followed by the digest. -/
def adOf (digest : CtxRomAuth.CtxDigest) : AssociatedData :=
  ⟨authentication.AD_CONTEXT.val ++ (digestBytes digest).val, by
    rw [List.length_append, authentication.AD_CONTEXT.property, (digestBytes digest).property]
    rfl⟩

/-- The Server ML-DSA key of the generic completed binding: not modelled and never read (all-zero). -/
def unmodeledPinKey : Std.Array Std.U8 1952#usize := ⟨List.replicate 1952 0#u8, by rw [List.length_replicate]; rfl⟩

/-- The request hash of the generic completed binding: not modelled and never read (all-zero). -/
def unmodeledInitHash : Std.Array Std.U8 64#usize := ⟨List.replicate 64 0#u8, by rw [List.length_replicate]; rfl⟩

/-- The completed binding a Beacon in InitSent hands to the stage after hashing its transcript to `digest`. -/
def completedOf (control : pqxdh.BeaconInitSent) (digest : CtxRomAuth.CtxDigest) :
    session.CompletedRegistrationBinding :=
  ⟨⟨control.expected_server_binding, unmodeledPinKey⟩, unmodeledInitHash, control.beacon_identity_public_key,
    digestBytes digest, adOf digest⟩

/-! ### Refinement and pure layout lemmas -/

/-- The digest array reads back as the digest. -/
theorem digestBytes_abs (digest : CtxRomAuth.CtxDigest) : absBytes (digestBytes digest) = digest.toList := by
  simp only [digestBytes, absBytes, List.map_map]
  conv_rhs => rw [← List.map_id digest.toList]
  exact List.map_congr_left fun byte _ => UInt8.ofNat_toNat

/-- The assembled associated data reads back as the model's context87 followed by the digest. -/
theorem adOf_bytes (digest : CtxRomAuth.CtxDigest) :
    absBytes (adOf digest) = associatedData digest.toList := by
  change (authentication.AD_CONTEXT.val ++ (digestBytes digest).val).map absByte = _
  rw [List.map_append]
  change absBytes authentication.AD_CONTEXT ++ absBytes (digestBytes digest) = _
  rw [TranscriptAuthInputsRefinement.ad_context_abs, digestBytes_abs]
  rfl

/-- The extracted assembler returns exactly `adOf` on the digest array. -/
theorem adOf_exact (digest : CtxRomAuth.CtxDigest) :
    authentication.assemble_associated_data (digestBytes digest) = ok (adOf digest) := by
  obtain ⟨output, run, bytes⟩ := TranscriptAuthInputsRefinement.assemble_associated_data_abs (digestBytes digest)
  have same : output = adOf digest :=
    Subtype.ext ((absBytes_inj_iff output (adOf digest)).mp (by rw [bytes, adOf_bytes, digestBytes_abs]))
  rw [run, same]

/-- Equal assembled associated data means equal digests. -/
theorem adOf_inj {left right : CtxRomAuth.CtxDigest} (same : absBytes (adOf left) = absBytes (adOf right)) :
    left = right := by
  rw [adOf_bytes, adOf_bytes] at same
  exact List.Vector.toList_injective (associatedData_inj _ _ same)

/-- The extracted transcript builder returns the model preimage. -/
theorem transcript_extracted (init : authentication.InitFields) (response : authentication.AdResponseFields) :
    ∃ output, authentication.build_record_ad_transcript init response = ok output ∧
      absBytes output = transcript (SessionTranscriptRefinement.absInit init)
        (SessionTranscriptRefinement.absResponse response) :=
  SessionTranscriptRefinement.build_record_ad_transcript_abs init response

/-- Response fields read from extracted arrays have the protocol widths. -/
theorem adResponse_wellFormed (identity ephemeral : PqxdhBeaconPhase2Preparation.Word32)
    (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext) (keyId : Std.U64) :
    (adResponse identity ephemeral ciphertext keyId).WellFormed := by
  constructor <;> simp [adResponse, SessionTranscriptRefinement.absResponse]

/-- The response fields of a Server candidate have the protocol widths. -/
theorem serverResponse_wellFormed (candidate : pqxdh.ServerRegistrationCandidate) :
    (serverResponse candidate).WellFormed :=
  adResponse_wellFormed _ _ _ _

/-- The first 33 transcript bytes are the identity buffer when it has the identity width. -/
theorem transcript_take_identity (init : InitFields) (response : ResponseFields)
    (width : init.identityKey.length = 33) : (transcript init response).take 33 = init.identityKey := by
  simp [transcript, encode, initBlock, List.append_assoc, width]

/-- A parsed identity buffer has the identity width. -/
theorem parseIdentity_length {encoded : Pqxdh.Bytes} {pk : PqxdhEd25519EufCma.Ed25519PublicKey}
    (parsed : PqxdhEd25519EufCma.parseIdentity encoded = some pk) : encoded.length = 33 := by
  rw [(PqxdhEd25519EufCma.parseIdentity_eq_some_iff encoded pk).mp parsed]
  exact PqxdhEd25519EufCma.encodedIdentity_length pk

/-- The completed binding carries the assembled associated data. -/
theorem completedOf_ad (control : pqxdh.BeaconInitSent) (digest : CtxRomAuth.CtxDigest) :
    (completedOf control digest).associated_data = adOf digest := rfl

/-! ### Leaves: from equal associated data to equal identities -/

/-- L1: outside a cache collision, equal assembled AD of two cached digests gives equal queries. -/
theorem query_eq_of_ad_eq (cache : CtxRomAuth.CtxRO.QueryCache) {left right : CtxRomAuth.CtxRO.Domain}
    {dl dr : CtxRomAuth.CtxDigest} (leftCached : cache left = some dl) (rightCached : cache right = some dr)
    (same : absBytes (adOf dl) = absBytes (adOf dr)) (collisionFree : ¬ CacheHasCollision cache) : left = right := by
  have digest := adOf_inj same
  subst digest
  exact cache_lookup_eq_of_noCollision collisionFree leftCached ⟨dl, rightCached, HEq.rfl⟩

/-- L1': the transcript form of `query_eq_of_ad_eq`. -/
theorem transcript_eq_of_ad_eq (cache : CtxRomAuth.CtxRO.QueryCache) {li ri : InitFields}
    {lr rr : ResponseFields} {dl dr : CtxRomAuth.CtxDigest}
    (leftCached : cache (query li lr) = some dl) (rightCached : cache (query ri rr) = some dr)
    (same : absBytes (adOf dl) = absBytes (adOf dr)) (collisionFree : ¬ CacheHasCollision cache) :
    transcript li lr = transcript ri rr :=
  congrArg Prod.snd (query_eq_of_ad_eq cache leftCached rightCached same collisionFree)

/-- L2: equal transcripts give equal identity buffers; only the two 33-byte identity widths are needed. -/
theorem identityKey_eq_of_transcript_eq {li ri : InitFields} {lr rr : ResponseFields}
    (lw : li.identityKey.length = 33) (rw : ri.identityKey.length = 33)
    (same : transcript li lr = transcript ri rr) : li.identityKey = ri.identityKey := by
  rw [← transcript_take_identity li lr lw, ← transcript_take_identity ri rr rw, same]

/-- L2': the verified identity of a received candidate equals the identity written by an honest Beacon. -/
theorem identity_of_transcript_eq (received : PqxdhEd25519EufCma.Phase1Candidate)
    (identity pk : PqxdhEd25519EufCma.Ed25519PublicKey) (keys : PqxdhEd25519EufCma.Phase1KeyTuple)
    (s₁ s₂ s₃ : PqxdhEd25519EufCma.Ed25519Signature)
    (parsed : PqxdhEd25519EufCma.parseIdentity received.identityKey = some identity)
    {lr rr : ResponseFields}
    (same : transcript (initOf received) lr =
      transcript (initOf (PqxdhJointPhase1SourceWriter.candidate pk keys s₁ s₂ s₃)) rr) :
    identity = pk := by
  have keyEq := identityKey_eq_of_transcript_eq (parseIdentity_length parsed)
    (PqxdhEd25519EufCma.encodedIdentity_length pk) same
  change received.identityKey = PqxdhEd25519EufCma.encodedIdentity pk at keyEq
  rw [keyEq, PqxdhEd25519EufCma.parseIdentity_encodedIdentity] at parsed
  exact (Option.some.inj parsed).symm

/-- L3: all fields from equal transcripts under the four width facts. -/
theorem fields_of_transcript_eq {li ri : InitFields} {lr rr : ResponseFields} (h₁ : li.WellFormed)
    (h₂ : ri.WellFormed) (h₃ : lr.WellFormed) (h₄ : rr.WellFormed)
    (same : transcript li lr = transcript ri rr) : li = ri ∧ lr = rr :=
  encode_inj h₁ h₂ h₃ h₄ same

/-- An accepted Phase-1 candidate has the protocol Init widths. -/
theorem accept_wellFormed (verifyFn : PqxdhEd25519EufCma.Ed25519PublicKey → Pqxdh.Bytes →
      PqxdhEd25519EufCma.Ed25519Signature → Bool)
    (candidate : PqxdhEd25519EufCma.Phase1Candidate) (pk : PqxdhEd25519EufCma.Ed25519PublicKey)
    (decoded : PqxdhEd25519EufCma.Phase1KeyTuple)
    (accepted : PqxdhEd25519EufCma.acceptPhase1Candidate verifyFn candidate = some (pk, decoded)) :
    (initOf candidate).WellFormed := by
  obtain ⟨identity, pqSignature, preSignature, oneSignature, pq, -, pre, -, one, -⟩ :=
    PqxdhEd25519EufCma.acceptPhase1Candidate_some_witness verifyFn candidate pk decoded accepted
  refine ⟨?_, ?_, ?_, ?_⟩
  · change candidate.identityKey.length = 33
    rw [identity]
    exact PqxdhEd25519EufCma.encodedIdentity_length pk
  · change candidate.preKey.length = 98
    simp [pre, PqxdhEd25519EufCma.attachSignature]
  · change candidate.oneTimeKey.length = 98
    simp [one, PqxdhEd25519EufCma.attachSignature]
  · change candidate.pqKey.length = 1249
    simp [pq, PqxdhEd25519EufCma.attachSignature]

/-- Width receipt of a candidate accepted by the Server's source acceptance, under the existing attached-verification adapter premise. -/
theorem verified_wellFormed (attachedVerify : PqxdhEd25519EufCma.Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : PqxdhJointIdentity.Primitives)
    (adapter : PqxdhEd25519EufCma.HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (candidate : PqxdhEd25519EufCma.Phase1Candidate) (identity : PqxdhEd25519EufCma.Ed25519PublicKey)
    (keys : PqxdhEd25519EufCma.Phase1KeyTuple)
    (accepted : PqxdhJointPhase1Reports.sourceAccept attachedVerify candidate = some (identity, keys)) :
    (initOf candidate).WellFormed :=
  accept_wellFormed primitives.verify candidate identity keys
    ((PqxdhJointPhase1Reports.sourceAccept_eq attachedVerify primitives adapter candidate).symm.trans accepted)

end BeaconcryptCore.Computational.PqxdhTranscriptAd

-- Axiom guards (generated from kernel output)

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.AssociatedData' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.AssociatedData

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.initOf' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.initOf

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.adResponse' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.adResponse

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.serverResponse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.serverResponse

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.transcript' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.transcript

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.query' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.query

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.digestBytes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.digestBytes

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.adOf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.adOf

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.unmodeledPinKey' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.unmodeledPinKey

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.unmodeledInitHash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.unmodeledInitHash

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.completedOf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.completedOf

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.digestBytes_abs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.digestBytes_abs

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.adOf_bytes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.adOf_bytes

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.adOf_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.adOf_exact

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.adOf_inj' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.adOf_inj

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.transcript_extracted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.transcript_extracted

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.adResponse_wellFormed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.adResponse_wellFormed

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.serverResponse_wellFormed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.serverResponse_wellFormed

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.transcript_take_identity' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.transcript_take_identity

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.parseIdentity_length' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.parseIdentity_length

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.completedOf_ad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.completedOf_ad

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.query_eq_of_ad_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.query_eq_of_ad_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.transcript_eq_of_ad_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.transcript_eq_of_ad_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.identityKey_eq_of_transcript_eq' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.identityKey_eq_of_transcript_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.identity_of_transcript_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.identity_of_transcript_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.fields_of_transcript_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.fields_of_transcript_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.accept_wellFormed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.accept_wellFormed

/--
info: 'BeaconcryptCore.Computational.PqxdhTranscriptAd.verified_wellFormed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhTranscriptAd.verified_wellFormed

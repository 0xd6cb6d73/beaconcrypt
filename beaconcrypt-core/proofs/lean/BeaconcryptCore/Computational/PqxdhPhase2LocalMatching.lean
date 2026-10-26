import BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer
import BeaconcryptCore.Computational.PqxdhServerRegistrationPublication
import BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins
import BeaconcryptCore.Computational.RawCtxCanonicalSeal
import BeaconcryptCore.Computational.RawCtxSharedPrimitive

/-!
# Phase 2 local matching: what the Beacon accepts when its first record matches a Server seal

This module is stage B9a of the Server-authentication proof (Milestone B, route R1). It is a component result about the Beacon's Phase 2 finish and the Server's registration seal. It reads no definition of the Server-authentication experiment and adds no premise to any existing theorem.

The Beacon finishes registration by opening the Server's sequence-one record with a local raw owner (`PqxdhBeaconPhase2Publication.localOwner`), which pins the Server's identity key ID as sender and uses the candidate's 281-byte associated data. The raw receive rejects any other sender before opening (`ratchet.rs:505-513`). The Beacon then requires sequence one and checks that the first eight plaintext bytes are the little-endian encoding of the assigned key ID from the Phase 2 response (`beacon.rs:462-484`, core `pqxdh.rs:616-628`). The Server seals exactly that binding followed by the payload, with its assigned key ID as target and its identity key ID as sender (`server.rs:463-477`, `PqxdhServerRegistrationPublication.firstContext`).

`matching_open` is the local-owner form of the existing matched-plaintext lemma: if the Beacon's record has the same full CTX tuple (nonce, associated data with sequence and sender, protected payload) as a correct successful seal under the key that opened it, the Beacon's plaintext, sequence and sender are exactly those of the seal. `accepted_of_match` then shows that the Beacon accepts exactly the sealed key ID, payload and associated data (`sealedFields`), using `afterOpening_success`, `plaintextBinding_bytes`, `registration_key_id_binding_abs` and `LE64_inj`. `fresh_of_differs` (every history entry records a key-ID-bound seal context with different sealed fields) and `fresh_forall` (the accepted fields differ from the sealed fields of every key-ID-bound context any entry records) state the contrapositive in the form the selected authentication observer reads, and `attempt_accepted` and `won_of_attempt` turn it into an observer win. `afterOpening_of_binding` is the converse of the binding gate, `relay_fields` checks on an honest relay that the Beacon's accepted fields and the Server's sealed fields agree, and `joint` shows that all premises of `accepted_of_match` hold together for every non-empty payload and every `Pqxdh.Crypto` whose seal of the bound payload has a non-empty body; the non-empty payload is necessary, because the Beacon's binding gate needs more than eight plaintext bytes.

The native results tie the opening key to the Beacon's installed kernel. `Reaches` records that the extracted receive admission of a kernel reaches an opening capability through KDF replies in the support of the interpreter, and `raw_reaches` shows that every present raw-owner reply, under every interpreter, opens such a capability of the owner's kernel with that capability's material. `KernelOpening` packages this for the Phase 2 local owner together with the run's own opening reply at the capability's arguments, ending in the run's final primitive state, the local target, and the ordinary AEAD opening under the source key, the key half of that material, so the key is the material the run opened with: `local_opening` proves it for every present local-owner reply under an interpreter whose AEAD branch is the ordinary functional opening, `afterRoot_opening` and `consumer_opening` prove it inside the Beacon's post-root tail and the related-root consumer's tail at the initial kernel installed from the initial KDF reply, with the supported getter replies and the raw-receive run, and `consumer_matching` combines it with `accepted_of_match`. These results do not identify the material with a Server session's key; that is left to the key-factoring stage. The shared-cache interpreter `RawCtxSharedPrimitive.nativeImpl` has an ordinary AEAD branch (`native_ordinary`).

Nothing here is a security statement. The primitive facts used are ordinary AEAD correctness (`Pqxdh.Crypto.aead_open_seal`), determinism of the abstract AEAD opening and the 16-byte tag length of the abstract seal (`Pqxdh.Crypto.aeadSeal_tag_length`), which `joint` uses to build its sealed record and the existing typed seal `ctxSeal` uses for its tag. Messages are abstract byte strings that each side decodes with a free function; no serialization-library behaviour and no internal property of libsodium is used.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open PqxdhRefinement BeaconcryptCore.Refinement BeaconcryptCore.Refinement.RepresentationBridge
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhPhase2LocalMatching
open CtxRomAuth
open PqxdhBeaconPhase2Publication (Staged afterOpening localOwner clearedCandidate)

/-! ## Accepted and sealed fields -/

/-- The fields a successful Phase 2 finish accepts: the assigned key ID it installs, the application payload after the 8-byte binding, and the session associated data. -/
def acceptedFields (staged : Staged) : Std.U64 × Pqxdh.Bytes × Pqxdh.Bytes :=
  (staged.authenticated.candidate.assigned_key_id, staged.opened.plaintext.drop 8, absBytes staged.associatedData)

/-- The same three fields read from a Server seal context: the target key ID, the plaintext after the 8-byte binding, and the associated data. -/
def sealedFields (context : RawCtxSourceSend.SealContext) : Std.U64 × Pqxdh.Bytes × Pqxdh.Bytes :=
  (context.targetId, context.plaintext.drop 8, context.associatedData)

/-- A seal context whose plaintext starts with the little-endian encoding of its target key ID, as every Server registration seal does. -/
def KeyIdBound (context : RawCtxSourceSend.SealContext) : Prop :=
  context.plaintext.take 8 = Pqxdh.LE64 context.targetId.val

/-- The Server's registration seal context binds its target key ID and carries the caller's payload after the binding, with the Server identity key ID as sender and the candidate's associated data. -/
theorem firstContext_bound (candidate : pqxdh.ServerRegistrationCandidate)
    (binding : pqxdh.RegistrationKeyIdBinding) (hbinding : candidate.key_id_binding = ok binding)
    (payload : Pqxdh.Bytes) :
    KeyIdBound (PqxdhServerRegistrationPublication.firstContext candidate (absBytes binding.bytes ++ payload)) ∧
      sealedFields (PqxdhServerRegistrationPublication.firstContext candidate (absBytes binding.bytes ++ payload)) =
        (candidate.key_id, payload, absBytes candidate.associated_data) ∧
      (PqxdhServerRegistrationPublication.firstContext candidate (absBytes binding.bytes ++ payload)).senderId =
        candidate.server_identity_key_id := by
  obtain ⟨actual, hactual, hbytes⟩ := PqxdhServerRegistrationPublication.candidate_binding candidate
  have same : actual = binding := RustM.ok.inj (hactual.symm.trans hbinding)
  subst same
  have hlength : (absBytes actual.bytes).length = 8 := by rw [hbytes, Pqxdh.LE64_length]
  refine ⟨?_, ?_, rfl⟩
  · change (absBytes actual.bytes ++ payload).take 8 = Pqxdh.LE64 candidate.key_id.val
    rw [List.take_left' hlength, hbytes]
  · change (candidate.key_id, (absBytes actual.bytes ++ payload).drop 8, absBytes candidate.associated_data) = _
    rw [List.drop_left' hlength]

/-! ## Binding authentication at the Beacon -/

/-- A staged Phase 2 success keeps the candidate unchanged, was sent by the pinned Server key ID, has sequence one, and its plaintext starts with the little-endian encoding of the candidate's assigned key ID. -/
theorem authenticated_binding (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : ConcreteRatchetKernel)
    (reply : core.option.Option RawCtxWholeOwner.Decrypted) (staged : Staged)
    (success : afterOpening candidate kernel reply = some staged) :
    reply = .Some staged.opened ∧ staged.authenticated.candidate = candidate ∧
      staged.opened.keyId = candidate.server_binding.identity_key_id ∧
      staged.opened.sequence = 1#u64 ∧ 8 < staged.opened.plaintext.length ∧
      staged.opened.plaintext.take 8 = Pqxdh.LE64 candidate.assigned_key_id.val ∧
      staged.associatedData = candidate.associated_data := by
  obtain ⟨hreply, hsequence, _, had, hlength, hauth⟩ :=
    PqxdhBeaconPhase2Publication.afterOpening_success candidate kernel reply staged success
  obtain ⟨binding, hbinding, hbytes⟩ := registration_key_id_binding_abs candidate.assigned_key_id
  unfold pqxdh.authenticate_registration_key_id_binding at hauth
  split at hauth
  · rename_i hsender
    simp only [pqxdh.BeaconRegistrationCandidate.key_id_binding, hbinding, bind_tc_ok, array_eq_abs] at hauth
    split at hauth
    · rename_i hequal
      have hcandidate := congrArg pqxdh.AuthenticatedBeaconRegistration.candidate
        (core.result.Result.Ok.inj (RustM.ok.inj hauth)).symm
      refine ⟨hreply, hcandidate, hsender, hsequence, hlength, ?_, had⟩
      rw [← ProtocolComposition.plaintextBinding_bytes staged.opened.plaintext hlength, of_decide_eq_true hequal,
        hbytes]
    · cases RustM.ok.inj hauth
  · cases RustM.ok.inj hauth

/-- If the Beacon's staged plaintext and associated data are those of a key-ID-bound seal context, the Beacon accepts exactly the sealed key ID, payload and associated data. -/
theorem accepted_of_plaintext (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : ConcreteRatchetKernel)
    (reply : core.option.Option RawCtxWholeOwner.Decrypted) (staged : Staged)
    (success : afterOpening candidate kernel reply = some staged)
    (context : RawCtxSourceSend.SealContext) (bound : KeyIdBound context)
    (plaintext : staged.opened.plaintext = context.plaintext)
    (associated : absBytes candidate.associated_data = context.associatedData) :
    acceptedFields staged = sealedFields context := by
  obtain ⟨_, hcandidate, _, _, _, hprefix, had⟩ := authenticated_binding candidate kernel reply staged success
  have hencoded : Pqxdh.LE64 candidate.assigned_key_id.val = Pqxdh.LE64 context.targetId.val := by
    rw [← hprefix, plaintext]
    exact bound
  have hkey : candidate.assigned_key_id = context.targetId :=
    UScalar.eq_of_val_eq (Pqxdh.LE64_inj candidate.assigned_key_id.bv.isLt context.targetId.bv.isLt hencoded)
  simp only [acceptedFields, sealedFields, hcandidate, hkey, plaintext, had, associated]

/-- A successful finish installs the accepted key ID and returns the accepted payload, so the accepted fields are readable from the finish output and the established phase. -/
theorem finish_fields {I D K : Type} (control : pqxdh.BeaconInitSent)
    (state next : PqxdhBeaconPhase2Preparation.State I D K) (staged : Staged) (payload : Pqxdh.Bytes)
    (success : PqxdhBeaconPhase2Publication.finish control state (some staged) = (some payload, next)) :
    acceptedFields staged = (next.beacon.identityKeyId, payload, absBytes staged.associatedData) ∧
      next.beacon.phase = .established
        ⟨staged.authenticated.candidate.server_binding, staged.authenticated.candidate.assigned_key_id⟩
        staged.associatedData staged.kernel := by
  obtain ⟨actual, same, _, _, published⟩ :=
    PqxdhBeaconPhase2Publication.finish_success control state next (some staged) payload success
  cases Option.some.inj same
  obtain ⟨hpayload, _, _, _, hkey, hphase, _⟩ := PqxdhBeaconPhase2Publication.publish_fields state staged
  rw [published] at hpayload hkey hphase
  exact ⟨by simp only [acceptedFields, ← hpayload, ← hkey], hphase⟩

/-- Completeness of the binding gate: a sequence-one reply from the pinned Server key ID whose plaintext is the little-endian assigned key ID followed by a non-empty payload is staged, with the candidate, its associated data and the kernel unchanged. -/
theorem afterOpening_of_binding (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : ConcreteRatchetKernel)
    (opened : RawCtxWholeOwner.Decrypted)
    (sender : opened.keyId = candidate.server_binding.identity_key_id) (sequence : opened.sequence = 1#u64)
    (payload : Pqxdh.Bytes) (nonempty : payload ≠ [])
    (plaintext : opened.plaintext = Pqxdh.LE64 candidate.assigned_key_id.val ++ payload) :
    afterOpening candidate kernel (.Some opened) = some ⟨⟨candidate⟩, candidate.associated_data, kernel, opened⟩ := by
  have hlength : 8 < opened.plaintext.length := by
    have positive : 0 < payload.length := List.length_pos_iff.mpr nonempty
    rw [plaintext, List.length_append, Pqxdh.LE64_length]
    omega
  obtain ⟨binding, hbinding, hbytes⟩ := registration_key_id_binding_abs candidate.assigned_key_id
  have hprefix : absBytes (ProtocolComposition.plaintextBinding opened.plaintext hlength) = absBytes binding.bytes := by
    rw [ProtocolComposition.plaintextBinding_bytes, hbytes, plaintext, List.take_left' (Pqxdh.LE64_length _)]
  have hauth : pqxdh.authenticate_registration_key_id_binding candidate opened.keyId
      (ProtocolComposition.plaintextBinding opened.plaintext hlength) = ok (.Ok ⟨candidate⟩) := by
    simp only [pqxdh.authenticate_registration_key_id_binding, sender, ↓reduceIte,
      pqxdh.BeaconRegistrationCandidate.key_id_binding, hbinding, bind_tc_ok, array_eq_abs, hprefix, decide_true]
  have hnormal : PqxdhBeaconPhase2Publication.normalAuthenticate candidate opened.keyId
      (ProtocolComposition.plaintextBinding opened.plaintext hlength) = .Ok ⟨candidate⟩ :=
    RustM.ok.inj ((PqxdhBeaconPhase2Publication.normalAuthenticate_exact _ _ _).symm.trans hauth)
  unfold afterOpening
  simp only [sequence, ne_eq, not_true_eq_false, ↓reduceIte, hlength, ↓reduceDIte, hnormal]

/-- Consistency of the two field readings on an honest relay: if the Beacon opens exactly the plaintext of the Server's registration seal with a non-empty payload, from the pinned sender at sequence one, and the Beacon candidate's assigned key ID and associated data are the Server candidate's, the Beacon stages the record and accepts exactly the sealed fields. -/
theorem relay_fields (server : pqxdh.ServerRegistrationCandidate) (binding : pqxdh.RegistrationKeyIdBinding)
    (hbinding : server.key_id_binding = ok binding) (payload : Pqxdh.Bytes) (nonempty : payload ≠ [])
    (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : ConcreteRatchetKernel)
    (opened : RawCtxWholeOwner.Decrypted)
    (assigned : candidate.assigned_key_id = server.key_id)
    (associated : candidate.associated_data = server.associated_data)
    (sender : opened.keyId = candidate.server_binding.identity_key_id) (sequence : opened.sequence = 1#u64)
    (plaintext : opened.plaintext =
      (PqxdhServerRegistrationPublication.firstContext server (absBytes binding.bytes ++ payload)).plaintext) :
    ∃ staged, afterOpening candidate kernel (.Some opened) = some staged ∧
      acceptedFields staged =
        sealedFields (PqxdhServerRegistrationPublication.firstContext server (absBytes binding.bytes ++ payload)) := by
  obtain ⟨actual, hactual, hbytes⟩ := PqxdhServerRegistrationPublication.candidate_binding server
  have same : actual = binding := RustM.ok.inj (hactual.symm.trans hbinding)
  subst same
  have bound := (firstContext_bound server actual hbinding payload).1
  have encoded : opened.plaintext = Pqxdh.LE64 candidate.assigned_key_id.val ++ payload := by
    rw [plaintext, assigned, ← hbytes]
    rfl
  have success := afterOpening_of_binding candidate kernel opened sender sequence payload nonempty encoded
  refine ⟨_, success, accepted_of_plaintext candidate kernel _ _ success _ bound plaintext ?_⟩
  rw [associated]
  rfl

/-! ## Full-tuple matching under ordinary AEAD -/

/-- The ordinary AEAD opening of a component target's body and tag, under its nonce and associated data and the given key, returns the given plaintext. -/
def Opens (c : Pqxdh.Crypto) (key : CtxKey) (target : CtxUnclaimedAcceptance.Target) (plaintext : Pqxdh.Bytes) : Prop :=
  c.aeadOpen key.toList target.nonce.toList target.context.ad.bytes target.record.body target.record.tag =
    some plaintext

/-- A successful CTX seal entry opens to its own plaintext under the key; this is one entry of `RawCtxSelectedPlaintextOrigins.HistoryCorrect`. -/
def SealCorrect (c : Pqxdh.Crypto) (key : CtxKey) (entry : CtxSuccessfulSeal) : Prop :=
  c.aeadOpen key.toList entry.input.nonce.toList entry.input.context.ad.bytes entry.record.body entry.record.tag =
    some entry.input.plaintext

/-- The existing history invariant is exactly correctness of every entry. -/
theorem historyCorrect_iff (c : Pqxdh.Crypto) (key : CtxKey) (history : List CtxSuccessfulSeal) :
    RawCtxSelectedPlaintextOrigins.HistoryCorrect c key history ↔ ∀ entry ∈ history, SealCorrect c key entry :=
  Iff.rfl

/-- A present reply of the canonical CTX opening is the ordinary AEAD opening of the target. -/
theorem opens_of_targetOpen (c : Pqxdh.Crypto) (key : CtxKey) (target : CtxUnclaimedAcceptance.Target)
    (expected : CtxDigest) (plaintext : Pqxdh.Bytes)
    (opened : AdaptiveCtxCanonical.targetOpen c key target expected = some plaintext) :
    Opens c key target plaintext := by
  unfold AdaptiveCtxCanonical.targetOpen at opened
  split at opened
  · exact opened
  · cases opened

/-- Every record produced by the typed CTX seal opens to its plaintext under the sealing key, by ordinary AEAD correctness. -/
theorem ctxSeal_correct (c : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput) (record : CtxRomRecord)
    (sealed : record ∈ support (ctxSeal c key input)) : SealCorrect c key ⟨input, record⟩ := by
  simp only [ctxSeal, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at sealed
  obtain ⟨_, _, rfl⟩ := sealed
  exact c.aead_open_seal _ _ _ _

/-- Ordinary AEAD determinism: a target with the same full tuple as a correct seal opens to that seal's plaintext. -/
theorem target_matching (c : Pqxdh.Crypto) (key : CtxKey) (target : CtxUnclaimedAcceptance.Target)
    (plaintext : Pqxdh.Bytes) (opens : Opens c key target plaintext)
    (entry : CtxSuccessfulSeal) (correct : SealCorrect c key entry)
    (same : target.toLegacy.sameFullTupleAsSuccessfulSeal entry) :
    plaintext = entry.input.plaintext := by
  obtain ⟨nonce, ad, record⟩ := AdaptiveCtxReplayDictionary.fullTuple_fields target entry same
  have body : target.record.body = entry.record.body := congrArg Pqxdh.RecordCipher.body record
  have tag : target.record.tag = entry.record.tag := congrArg Pqxdh.RecordCipher.tag record
  unfold Opens at opens
  rw [nonce, ad, body, tag, correct] at opens
  exact (Option.some.inj opens).symm

/-! ## The Phase 2 local owner -/

/-- The key-free component target of a delivery to the Phase 2 local owner of `candidate`: the raw bytes are non-empty and decode to a frame that the owner validated against the pinned Server key ID and the candidate's associated data, the returned API value carries that frame's sender and sequence, and the target is the frame's CTX target under some nonce. -/
def LocalTarget (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (candidate : pqxdh.BeaconRegistrationCandidate) (opened : RawCtxWholeOwner.Decrypted)
    (target : CtxUnclaimedAcceptance.Target) : Prop :=
  ∃ (frame : RawCtxReceive.DecodedFrame) (nonce : CtxNonce) (slices : RawCtxFrameDecoding.Slices)
    (parsed : RawCtxFrameDecoding.fromPayload frame.payload = some slices)
    (width : (absBytes candidate.associated_data).length = 281),
    raw.isEmpty = false ∧ decode raw = some frame ∧
      RawCtxReceive.ValidFrame candidate.server_binding.identity_key_id (absBytes candidate.associated_data) frame ∧
      opened.keyId = frame.sender ∧ opened.sequence = frame.sequence ∧
      target = RawCtxKeyFreeDecoder.target nonce frame.sequence frame (absBytes candidate.associated_data)
        slices parsed width

/-- The local target carries the candidate's associated data, the API sequence and the pinned sender in its CTX context. -/
theorem localTarget_context (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (candidate : pqxdh.BeaconRegistrationCandidate) (opened : RawCtxWholeOwner.Decrypted)
    (target : CtxUnclaimedAcceptance.Target) (delivery : LocalTarget decode raw candidate opened target) :
    target.context.ad = ⟨absBytes candidate.associated_data, opened.sequence.val, opened.keyId.val⟩ ∧
      opened.keyId = candidate.server_binding.identity_key_id ∧
      ∃ frame, decode raw = some frame ∧ target.record.encode = frame.payload := by
  obtain ⟨frame, nonce, slices, parsed, width, _, decoded, valid, key, sequence, rfl⟩ := delivery
  refine ⟨?_, key.trans valid.1, frame, decoded, RawCtxSelectedPlaintextOrigins.record_payload frame slices parsed⟩
  simp only [RawCtxKeyFreeDecoder.target, key, sequence]

/-- Matched opening for the Phase 2 local owner: if the Beacon's local target opens to its plaintext under some key and has the same full CTX tuple as a correct seal under that key, the Beacon's plaintext, sequence and sender are the seal's, the seal's associated data is the candidate's, its sender is the pinned Server key ID, and the protected payloads agree. -/
theorem matching_open (c : Pqxdh.Crypto) (key : CtxKey) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (candidate : pqxdh.BeaconRegistrationCandidate) (opened : RawCtxWholeOwner.Decrypted)
    (target : CtxUnclaimedAcceptance.Target) (delivery : LocalTarget decode raw candidate opened target)
    (opens : Opens c key target opened.plaintext)
    (entry : CtxSuccessfulSeal) (correct : SealCorrect c key entry)
    (same : target.toLegacy.sameFullTupleAsSuccessfulSeal entry) :
    opened.plaintext = entry.input.plaintext ∧
      entry.input.context.ad = ⟨absBytes candidate.associated_data, opened.sequence.val, opened.keyId.val⟩ ∧
      opened.keyId = candidate.server_binding.identity_key_id ∧ entry.input.nonce = target.nonce ∧
      ∃ frame, decode raw = some frame ∧ frame.payload = entry.record.encode := by
  obtain ⟨ad, pinned, frame, decoded, payload⟩ := localTarget_context decode raw candidate opened target delivery
  exact ⟨target_matching c key target opened.plaintext opens entry correct same, same.2.1.symm.trans ad,
    pinned, same.1.symm, frame, decoded, payload.symm.trans same.2.2⟩

/-- A CTX seal entry records the plaintext, associated data and sender of a source seal context. -/
def Records (entry : CtxSuccessfulSeal) (context : RawCtxSourceSend.SealContext) : Prop :=
  entry.input.plaintext = context.plaintext ∧ entry.input.context.ad.bytes = context.associatedData ∧
    entry.input.context.ad.sid = context.senderId.val

/-- The typed CTX seal input of a source seal records that seal's context, and its sequence is the seal's sequence. -/
theorem sourceInput_records (input : RawCtxSourceSend.SealInput) (had : input.context.associatedData.length = 281)
    (record : CtxRomRecord) :
    Records ⟨RawCtxCanonicalSeal.sourceInput input had, record⟩ input.context ∧
      (RawCtxCanonicalSeal.sourceInput input had).context.ad.seq = input.sequence.val :=
  ⟨⟨rfl, rfl, rfl⟩, rfl⟩

/-- Accepted fields of a match: if a staged Phase 2 success opened a local target that has the same full CTX tuple as a correct seal entry recording a key-ID-bound seal context, the Beacon accepts exactly that seal's key ID, payload and associated data, and the seal was sent by the pinned Server key ID. -/
theorem accepted_of_match (c : Pqxdh.Crypto) (key : CtxKey)
    (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : ConcreteRatchetKernel)
    (reply : core.option.Option RawCtxWholeOwner.Decrypted) (staged : Staged)
    (success : afterOpening candidate kernel reply = some staged)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (target : CtxUnclaimedAcceptance.Target)
    (delivery : LocalTarget decode raw candidate staged.opened target)
    (opens : Opens c key target staged.opened.plaintext)
    (entry : CtxSuccessfulSeal) (correct : SealCorrect c key entry)
    (same : target.toLegacy.sameFullTupleAsSuccessfulSeal entry)
    (context : RawCtxSourceSend.SealContext) (records : Records entry context) (bound : KeyIdBound context) :
    acceptedFields staged = sealedFields context ∧ context.senderId = candidate.server_binding.identity_key_id ∧
      entry.input.context.ad.seq = 1 := by
  obtain ⟨plaintext, ad, pinned, _⟩ := matching_open c key decode raw candidate staged.opened target delivery opens
    entry correct same
  obtain ⟨_, _, _, sequence, _⟩ := authenticated_binding candidate kernel reply staged success
  have associated : absBytes candidate.associated_data = context.associatedData := by
    rw [← records.2.1, ad]
  have sender : context.senderId.val = candidate.server_binding.identity_key_id.val := by
    rw [← records.2.2, ad, pinned]
  refine ⟨accepted_of_plaintext candidate kernel reply staged success context bound
    (plaintext.trans records.1) associated, UScalar.eq_of_val_eq sender, ?_⟩
  rw [ad, sequence]
  rfl

/-- Contrapositive for the authentication observer: if every entry of a correct history records some key-ID-bound seal context whose sealed fields differ from the Beacon's accepted fields, the Beacon's local target has no full-tuple match in that history. -/
theorem fresh_of_differs (c : Pqxdh.Crypto) (key : CtxKey)
    (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : ConcreteRatchetKernel)
    (reply : core.option.Option RawCtxWholeOwner.Decrypted) (staged : Staged)
    (success : afterOpening candidate kernel reply = some staged)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (target : CtxUnclaimedAcceptance.Target)
    (delivery : LocalTarget decode raw candidate staged.opened target)
    (opens : Opens c key target staged.opened.plaintext)
    (history : List CtxSuccessfulSeal) (correct : RawCtxSelectedPlaintextOrigins.HistoryCorrect c key history)
    (differs : ∀ entry ∈ history, ∃ context, Records entry context ∧ KeyIdBound context ∧
      acceptedFields staged ≠ sealedFields context) :
    ∀ entry ∈ history, ¬ target.toLegacy.sameFullTupleAsSuccessfulSeal entry := by
  intro entry member same
  obtain ⟨context, records, bound, different⟩ := differs entry member
  exact different (accepted_of_match c key candidate kernel reply staged success decode raw target delivery opens
    entry (correct entry member) same context records bound).1

/-- Universal form of `fresh_of_differs`: if the Beacon's accepted fields differ from the sealed fields of every key-ID-bound seal context that any entry of a correct history records, the Beacon's local target has no full-tuple match in that history. Entries that record no key-ID-bound context impose nothing. -/
theorem fresh_forall (c : Pqxdh.Crypto) (key : CtxKey)
    (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : ConcreteRatchetKernel)
    (reply : core.option.Option RawCtxWholeOwner.Decrypted) (staged : Staged)
    (success : afterOpening candidate kernel reply = some staged)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (target : CtxUnclaimedAcceptance.Target)
    (delivery : LocalTarget decode raw candidate staged.opened target)
    (opens : Opens c key target staged.opened.plaintext)
    (history : List CtxSuccessfulSeal) (correct : RawCtxSelectedPlaintextOrigins.HistoryCorrect c key history)
    (differs : ∀ entry ∈ history, ∀ context, Records entry context → KeyIdBound context →
      acceptedFields staged ≠ sealedFields context) :
    ∀ entry ∈ history, ¬ target.toLegacy.sameFullTupleAsSuccessfulSeal entry := by
  intro entry member same
  obtain ⟨plaintext, ad, _⟩ := matching_open c key decode raw candidate staged.opened target delivery opens
    entry (correct entry member) same
  obtain ⟨_, _, _, _, _, hprefix, _⟩ := authenticated_binding candidate kernel reply staged success
  let context : RawCtxSourceSend.SealContext :=
    ⟨entry.input.plaintext, candidate.assigned_key_id, staged.opened.keyId, entry.input.context.ad.bytes⟩
  have records : Records entry context := ⟨rfl, rfl, by rw [ad]⟩
  have bound : KeyIdBound context := by
    change entry.input.plaintext.take 8 = _
    rw [← plaintext, hprefix]
  exact differs entry member context records bound (accepted_of_match c key candidate kernel reply staged success
    decode raw target delivery opens entry (correct entry member) same context records bound).1

/-- A present reply whose decoded target has no full-tuple match in the attempt-time history is an accepted attempt of the selected authentication observer. -/
theorem attempt_accepted (rawDecode : AdaptiveCtxReceive.RawDecoder) (bytes : Pqxdh.Bytes)
    (target : CtxUnclaimedAcceptance.Target) (decoded : rawDecode bytes = some target)
    (plaintext : Pqxdh.Bytes) (history : List CtxSuccessfulSeal)
    (fresh : ∀ entry ∈ history, ¬ target.toLegacy.sameFullTupleAsSuccessfulSeal entry) :
    RawCtxSelectedAuthenticationObserver.accepted rawDecode ⟨bytes, some plaintext, history⟩ = true :=
  (RawCtxSelectedAuthenticationObserver.accepted_iff rawDecode _).mpr
    ⟨target, decoded, Option.some_ne_none plaintext, fresh⟩

/-- An observer state that contains such an accepted attempt is won. -/
theorem won_of_attempt (rawDecode : AdaptiveCtxReceive.RawDecoder) (state : RawCtxSelectedAuthenticationObserver.State)
    (attempt : RawCtxSelectedAuthenticationObserver.Attempt) (member : attempt ∈ state.attempts)
    (accepted : RawCtxSelectedAuthenticationObserver.accepted rawDecode attempt = true) :
    RawCtxSelectedAuthenticationObserver.won rawDecode state = true :=
  List.any_eq_true.mpr ⟨attempt, member, accepted⟩

/-- Joint satisfiability of every premise of `accepted_of_match`, for every non-empty payload and every `Pqxdh.Crypto` whose seal of the binding-prefixed payload has a non-empty body (the non-empty payload is necessary, since the binding gate needs more than eight plaintext bytes): a correctly bound sequence-one delivery whose frame carries that seal is staged, is a local target, opens to its plaintext and fully matches the correct seal entry, and the entry records a key-ID-bound context whose sealed fields are the assigned key ID, the payload and the candidate's associated data. -/
theorem joint (c : Pqxdh.Crypto) (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : ConcreteRatchetKernel)
    (key : CtxKey) (nonce : CtxNonce) (commit : CtxDigest) (payload : Pqxdh.Bytes) (nonempty : payload ≠ [])
    (body : (c.aeadSeal key.toList nonce.toList (absBytes candidate.associated_data)
      (Pqxdh.LE64 candidate.assigned_key_id.val ++ payload)).1 ≠ []) :
    ∃ (staged : Staged) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
      (target : CtxUnclaimedAcceptance.Target) (entry : CtxSuccessfulSeal) (context : RawCtxSourceSend.SealContext),
      afterOpening candidate kernel (.Some staged.opened) = some staged ∧
      LocalTarget decode raw candidate staged.opened target ∧ Opens c key target staged.opened.plaintext ∧
      SealCorrect c key entry ∧ target.toLegacy.sameFullTupleAsSuccessfulSeal entry ∧ Records entry context ∧
      KeyIdBound context ∧ acceptedFields staged = sealedFields context ∧
      sealedFields context = (candidate.assigned_key_id, payload, absBytes candidate.associated_data) := by
  let pinned := candidate.server_binding.identity_key_id
  let plaintext := Pqxdh.LE64 candidate.assigned_key_id.val ++ payload
  let opened : RawCtxWholeOwner.Decrypted := ⟨plaintext, pinned, 1#u64⟩
  have success := afterOpening_of_binding candidate kernel opened rfl rfl payload nonempty rfl
  have width : (absBytes candidate.associated_data).length = 281 := by simp
  let context : CtxRecordContext :=
    ⟨⟨absBytes candidate.associated_data, (1#u64 : Std.U64).val, pinned.val⟩, width,
      (1#u64 : Std.U64).bv.isLt, pinned.bv.isLt⟩
  let sealed := c.aeadSeal key.toList nonce.toList (absBytes candidate.associated_data) plaintext
  have tagLength : sealed.2.length = 16 := c.aeadSeal_tag_length _ _ _ _
  let record : CtxRomRecord := ⟨sealed.1, sealed.2, tagLength, commit⟩
  let entry : CtxSuccessfulSeal := ⟨⟨nonce, context, plaintext⟩, record⟩
  let frame : RawCtxReceive.DecodedFrame := ⟨1#u64, pinned, record.encode⟩
  have long : 80 < frame.payload.length := by
    have positive : 0 < sealed.1.length := List.length_pos_iff.mpr body
    change 80 < (sealed.1 ++ sealed.2 ++ commit.toList).length
    simp only [List.length_append, tagLength, List.Vector.toList_length]
    omega
  obtain ⟨slices, parsed⟩ : ∃ slices, RawCtxFrameDecoding.fromPayload frame.payload = some slices := by
    unfold RawCtxFrameDecoding.fromPayload
    split
    · omega
    · exact ⟨_, rfl⟩
  let target := RawCtxKeyFreeDecoder.target nonce frame.sequence frame (absBytes candidate.associated_data)
    slices parsed width
  have same : target.toLegacy.sameFullTupleAsSuccessfulSeal entry :=
    ⟨rfl, rfl, RawCtxSelectedPlaintextOrigins.record_payload frame slices parsed⟩
  obtain ⟨_, _, fields⟩ := AdaptiveCtxReplayDictionary.fullTuple_fields target entry same
  have hbody : target.record.body = sealed.1 := congrArg Pqxdh.RecordCipher.body fields
  have htag : target.record.tag = sealed.2 := congrArg Pqxdh.RecordCipher.tag fields
  have delivery : LocalTarget (fun _ => some frame) [0] candidate opened target :=
    ⟨frame, nonce, slices, parsed, width, rfl, rfl, ⟨rfl, long, width⟩, rfl, rfl, rfl⟩
  have opens : Opens c key target opened.plaintext := by
    change c.aeadOpen key.toList nonce.toList (absBytes candidate.associated_data) target.record.body
      target.record.tag = some plaintext
    rw [hbody, htag]
    exact c.aead_open_seal _ _ _ _
  have correct : SealCorrect c key entry := c.aead_open_seal _ _ _ _
  let sealContext : RawCtxSourceSend.SealContext :=
    ⟨plaintext, candidate.assigned_key_id, pinned, absBytes candidate.associated_data⟩
  have records : Records entry sealContext := ⟨rfl, rfl, rfl⟩
  have bound : KeyIdBound sealContext := List.take_left' (Pqxdh.LE64_length _)
  have sealedEq : sealedFields sealContext =
      (candidate.assigned_key_id, payload, absBytes candidate.associated_data) := by
    simp only [sealedFields, sealContext, plaintext, List.drop_left' (Pqxdh.LE64_length _)]
  have main := accepted_of_match c key candidate kernel (.Some opened) _ success (fun _ => some frame) [0] target
    delivery opens entry correct same sealContext records bound
  exact ⟨_, fun _ => some frame, [0], target, entry, sealContext, success, delivery, opens, correct, same, records,
    bound, main.1, sealedEq⟩

/-! ## Native provenance of the local target -/

/-- A native primitive interpretation whose AEAD branch returns the ordinary functional opening `RawCtxSourceOpen.baseOpen`; its KDF and hash branches are unrestricted. -/
def OrdinaryOpen {σ ι : Type} {base : OracleSpec ι} (c : Pqxdh.Crypto)
    (impl : QueryImpl RawCtxSourceOpen.NativeSpec (StateT σ (OracleComp base))) : Prop :=
  ∀ (input : RawCtxSourceOpen.BaseInput) (state : σ) (result : Option Pqxdh.Bytes × σ),
    result ∈ support ((impl (.inr (.inr input))).run state) → result.1 = RawCtxSourceOpen.baseOpen c input

/-- The shared-cache native interpreter, with any KDF interpretation, has the ordinary AEAD branch. -/
theorem native_ordinary {Auxiliary : Type} (c : Pqxdh.Crypto)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)) :
    OrdinaryOpen c (RawCtxSharedPrimitive.nativeImpl c kdf) := by
  intro input state result supported
  change result ∈ support (pure (RawCtxSourceOpen.baseOpen c input, state) : ProbComp _) at supported
  rw [support_pure, Set.mem_singleton_iff] at supported
  rw [supported]

/-- The receive effect `effect`, entered in primitive state `state`, reaches the opening capability `pending` in state `final`: either it is that capability, or it requests one KDF step on its chain and label, the reply is in the support of `kdf` at that request, and the resumed effect reaches the capability. -/
inductive Reaches {σ ι : Type} {base : OracleSpec ι} {Context : Type}
    (kdf : SymmetricRatchetKdfRequest → StateT σ (OracleComp base) RatchetKdfResponse) :
    σ → ReceiveEffect Context → ReceiveOpen Context → σ → Prop where
  | opened (state : σ) (pending : ReceiveOpen Context) :
      Reaches kdf state (.ReceiveOpenRequested pending) pending state
  | resume (state : σ) (request : ReceiveKdf Context) (response : RatchetKdfResponse) (next : σ)
      (pending : ReceiveOpen Context) (final : σ)
      (supported : (response, next) ∈ support ((kdf request.request).run state))
      (tail : Reaches kdf next (RawCtxOwnerOracle.resume request response) pending final) :
      Reaches kdf state (.ReceiveKdfRequested request) pending final

/-- Reaching transfers to any KDF interpretation whose support contains the original one's. -/
theorem reaches_mono {σ ι : Type} {base : OracleSpec ι} {Context : Type}
    {kdf other : SymmetricRatchetKdfRequest → StateT σ (OracleComp base) RatchetKdfResponse}
    (contained : ∀ request state result, result ∈ support ((kdf request).run state) →
      result ∈ support ((other request).run state))
    {state : σ} {effect : ReceiveEffect Context} {pending : ReceiveOpen Context} {final : σ}
    (reached : Reaches kdf state effect pending final) : Reaches other state effect pending final := by
  induction reached with
  | opened state pending => exact .opened state pending
  | resume state request response next pending final supported _ ih =>
      exact .resume state request response next pending final (contained _ _ _ supported) ih

/-- A reached capability keeps the target sequence and context that the entry effect was scoped to. -/
theorem reaches_scope {σ ι : Type} {base : OracleSpec ι} {Context : Type}
    {kdf : SymmetricRatchetKdfRequest → StateT σ (OracleComp base) RatchetKdfResponse}
    {state : σ} {effect : ReceiveEffect Context} {pending : ReceiveOpen Context} {final : σ}
    (reached : Reaches kdf state effect pending final) (target : Std.U64) (context : Context)
    (scope : RawCtxOwnerProvenance.Scope target context effect) :
    pending.sequence = ok target ∧ pending.context = context := by
  induction reached with
  | opened state pending => exact scope
  | resume state request response next pending final _ _ ih =>
      exact ih (by simpa only [scope.1, scope.2] using RawCtxOwnerProvenance.oracle_resume_scope request response)

/-- A supported receive execution with a present reply opened a capability that its entry effect reaches through the interpreter's KDF replies, and the reply is in the support of the opening callback at that capability. -/
theorem reaches_of_supported {σ ι Context Plaintext : Type} {base : OracleSpec ι}
    {impl : QueryImpl (RawCtxOwnerOracle.ReceiveSpec Context Plaintext) (StateT σ (OracleComp base))}
    {entry : σ × ReceiveEffect Context} {result : (ConcreteRatchetKernel × core.option.Option Plaintext) × σ}
    {qKdf qOpen : Nat} (run : RawCtxOwnerOracle.SupportedExecution impl entry result qKdf qOpen)
    (plaintext : Plaintext) (success : result.1.2 = .Some plaintext) :
    ∃ pending final, Reaches (fun request => impl (.inl request)) entry.1 entry.2 pending final ∧
      (.Some plaintext, result.2) ∈ support ((impl (.inr pending)).run final) := by
  induction run with
  | rejected => cases success
  | opened state pending reply nextState hsupport =>
      exact ⟨pending, state, .opened state pending, success ▸ hsupport⟩
  | resume state pending response nextState result qKdf qOpen hsupport _ ih =>
      obtain ⟨opened, final, reached, reply⟩ := ih success
      exact ⟨opened, final, .resume state pending response nextState opened final hsupport reached, reply⟩

/-- Kernel provenance of a present raw-owner reply, under every primitive interpretation: the delivery decodes to a validated frame, the opening capability is reached from the extracted receive admission of the owner's kernel at the frame's sequence and delivery context through supported KDF replies, its arguments carry the capability's material, and the returned API value wraps the opening reply. -/
theorem raw_reaches {Metadata σ ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT σ (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (state : RawCtxWholeOwner.OwnerState Metadata)
    (primitive : σ)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxWholeOwner.OwnerState Metadata) × σ)
    (supported : result ∈ support (RawCtxWholeOwner.rawGame impl decode raw state primitive))
    (message : RawCtxWholeOwner.Decrypted) (success : result.1.1 = .Some message) :
    ∃ (frame : RawCtxReceive.DecodedFrame) (pending : ReceiveOpen RawCtxWholeOwner.OpenContext)
      (input : RawCtxWholeOwner.OpenInput) (plaintext : Pqxdh.Bytes) (final : σ),
      decode raw = some frame ∧
      RawCtxReceive.ValidFrame state.owner.expectedSender state.owner.associatedData frame ∧
      Reaches (fun request => impl (.inl request)) primitive
        (RawCtxOwnerOracle.begin state.owner.kernel frame.sequence ⟨raw, frame, state.owner.associatedData⟩)
        pending final ∧
      RawCtxWholeOwner.arguments pending = some input ∧ pending.material = ok (.Some input.material) ∧
      input.sequence = frame.sequence ∧ input.context = ⟨raw, frame, state.owner.associatedData⟩ ∧
      message = RawCtxWholeOwner.decrypted input plaintext ∧
      (.Some plaintext, result.2) ∈ support ((impl (.inr input)).run final) := by
  unfold RawCtxWholeOwner.rawGame RawCtxWholeOwner.rawReceive StateT.run at supported
  split at supported
  all_goals repeat' split at supported
  all_goals try unfold StateT.run at supported
  all_goals try split at supported
  all_goals change result ∈ support ((simulateQ impl _).run primitive) at supported
  all_goals simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  all_goals try { subst result; cases success }
  obtain ⟨opened, hopen, rfl⟩ := supported
  rw [← QueryImpl.simulateQ_compose] at hopen
  unfold RawCtxOwnerOracle.receive at hopen
  obtain ⟨_, _, run⟩ := RawCtxOwnerOracle.supported_execution (impl ∘ₛ RawCtxWholeOwner.adapter) primitive _
    opened hopen
  obtain ⟨pending, final, reached, hreply⟩ := reaches_of_supported run message success
  have scope := reaches_scope reached _ _ (RawCtxOwnerProvenance.oracle_begin_scope _ _ _)
  obtain ⟨input, plaintext, hargs, hmessage, hinput⟩ :=
    RawCtxOwnerProvenance.adapter_success impl pending final opened.2 message hreply
  obtain ⟨hmaterial, hsequence, hcontext⟩ := RawCtxWholeOwner.arguments_some pending input hargs
  have kdf : ∀ request state result,
      result ∈ support (((impl ∘ₛ RawCtxWholeOwner.adapter) (.inl request)).run state) →
        result ∈ support ((impl (.inl request)).run state) := by
    intro request state result member
    rwa [show (impl ∘ₛ RawCtxWholeOwner.adapter) (.inl request) = impl (.inl request) from
      simulateQ_spec_query impl (.inl request)] at member
  exact ⟨_, pending, input, plaintext, final, by assumption, by assumption, reaches_mono kdf reached, hargs,
    hmaterial, RustM.ok.inj (hsequence.symm.trans scope.1), hcontext.trans scope.2, hmessage, hinput⟩

/-- A present reply of a raw owner receive needs non-empty raw bytes, under every primitive interpretation. -/
theorem raw_nonempty {Metadata σ ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT σ (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (state : RawCtxWholeOwner.OwnerState Metadata)
    (primitive : σ)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxWholeOwner.OwnerState Metadata) × σ)
    (supported : result ∈ support (RawCtxWholeOwner.rawGame impl decode raw state primitive))
    (opened : RawCtxWholeOwner.Decrypted) (success : result.1.1 = .Some opened) : raw.isEmpty = false := by
  unfold RawCtxWholeOwner.rawGame RawCtxWholeOwner.rawReceive StateT.run at supported
  split at supported
  · change result ∈ support ((simulateQ impl
        (pure (RawCtxWholeOwner.publish state (state.owner.kernel, .None)))).run primitive) at supported
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    cases success
  · rename_i nonempty
    exact Bool.eq_false_iff.mpr nonempty

/-- Kernel opening of the Phase 2 local owner of `candidate` with installed kernel `kernel`, entered in primitive state `primitive` and left in state `after`, for the delivery `raw` and returned value `opened`: an opening capability is reached from the extracted receive admission of `kernel` at the frame's sequence and the delivery context, through KDF replies in the support of the native interpreter's KDF branch, in some state `final`; the opening arguments `input` carry that capability's material; the opening callback at `input`, run from `final`, returns the present plaintext and ends in `after`; the delivery context holds `raw` and the candidate's associated data; the input sequence is the frame's; the selected target of `input` is a local target of the delivery; and that target opens to the returned plaintext under the source key of `input`, which is the key half of the capability's material. -/
def KernelOpening {σ ι : Type} {base : OracleSpec ι} (c : Pqxdh.Crypto)
    (impl : QueryImpl RawCtxSourceOpen.NativeSpec (StateT σ (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (candidate : pqxdh.BeaconRegistrationCandidate)
    (kernel : ConcreteRatchetKernel) (primitive after : σ) (opened : RawCtxWholeOwner.Decrypted)
    (input : RawCtxWholeOwner.OpenInput) (slices : RawCtxFrameDecoding.Slices)
    (parsed : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices)
    (width : input.context.associatedData.length = 281) : Prop :=
  (∃ (pending : ReceiveOpen RawCtxWholeOwner.OpenContext) (final : σ),
    Reaches (fun request => impl (.inl request)) primitive
      (RawCtxOwnerOracle.begin kernel input.context.frame.sequence input.context) pending final ∧
    RawCtxWholeOwner.arguments pending = some input ∧ pending.material = ok (.Some input.material) ∧
    (.Some opened.plaintext, after) ∈ support
      (((impl ∘ₛ RawCtxSourceOpen.nativeAdapter) (.inr input)).run final)) ∧
  input.context.raw = raw ∧ input.context.associatedData = absBytes candidate.associated_data ∧
  input.sequence = input.context.frame.sequence ∧
  LocalTarget decode raw candidate opened (RawCtxCanonicalOpening.selectedTarget input slices parsed width) ∧
  Opens c (RawCtxSourceOpen.sourceKey input) (RawCtxCanonicalOpening.selectedTarget input slices parsed width)
    opened.plaintext

/-- The source key of an opening input is the key half of its ratchet material. -/
theorem sourceKey_material (input : RawCtxWholeOwner.OpenInput) :
    (RawCtxSourceOpen.sourceKey input).toList = (absMaterial input.material).1 :=
  rfl

/-- Native provenance at the Phase 2 local owner: under a native interpreter with the ordinary AEAD branch, every present reply of the local owner with installed kernel `kernel` has a kernel opening that ends in the run's final primitive state. The run's reply and final state come from the opening callback at arguments `input` whose material is that of a capability the admission of `kernel` reaches, so the key the run opened with is the key half of that material. -/
theorem local_opening {σ ι : Type} {base : OracleSpec ι} (c : Pqxdh.Crypto)
    (impl : QueryImpl RawCtxSourceOpen.NativeSpec (StateT σ (OracleComp base))) (ordinary : OrdinaryOpen c impl)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (candidate : pqxdh.BeaconRegistrationCandidate)
    (kernel : ConcreteRatchetKernel) (primitive : σ)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxWholeOwner.OwnerState Unit) × σ)
    (supported : result ∈ support (RawCtxWholeOwner.rawGame (impl ∘ₛ RawCtxSourceOpen.nativeAdapter) decode raw
      (localOwner candidate kernel) primitive))
    (opened : RawCtxWholeOwner.Decrypted) (success : result.1.1 = .Some opened) :
    ∃ (input : RawCtxWholeOwner.OpenInput) (slices : RawCtxFrameDecoding.Slices)
      (parsed : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices)
      (width : input.context.associatedData.length = 281),
      KernelOpening c impl decode raw candidate kernel primitive result.2 opened input slices parsed width := by
  have nonempty := raw_nonempty _ decode raw _ primitive result supported opened success
  obtain ⟨frame, pending, input, plaintext, final, decoded, valid, reached, hargs, hmaterial, sequence, context,
    message, reply⟩ := raw_reaches (impl ∘ₛ RawCtxSourceOpen.nativeAdapter) decode raw _ primitive result
      supported opened success
  have kdf : ∀ request state result,
      result ∈ support (((impl ∘ₛ RawCtxSourceOpen.nativeAdapter) (.inl request)).run state) →
        result ∈ support ((impl (.inl request)).run state) := by
    intro request state result member
    rwa [show (impl ∘ₛ RawCtxSourceOpen.nativeAdapter) (.inl request) = impl (.inl request) from
      simulateQ_spec_query impl (.inl request)] at member
  have link := reply
  change (some plaintext, result.2) ∈ support ((simulateQ impl
    (simulateQ RawCtxSourceOpen.openLift (RawCtxSourceOpen.openInput input))).run final) at reply
  rw [← QueryImpl.simulateQ_compose] at reply
  obtain ⟨slices, _, parsed, _, _, aead⟩ :=
    RawCtxSourceOpen.openInput_success (impl ∘ₛ RawCtxSourceOpen.openLift) input final result.2 plaintext reply
  rw [RawCtxSourceOpen.openLift_apply] at aead
  have hplain : some plaintext = RawCtxSourceOpen.baseOpen c (RawCtxSourceOpen.baseInput input slices) :=
    ordinary _ _ _ aead
  have reachedNative := reaches_mono kdf reached
  obtain ⟨material, inputSequence, inputContext⟩ := input
  simp only at context sequence
  subst context sequence message
  have width : (absBytes candidate.associated_data).length = 281 := valid.2.2
  refine ⟨_, slices, parsed, width, ⟨pending, final, reachedNative, hargs, hmaterial, link⟩, rfl, rfl, rfl,
    ⟨frame, _, slices, parsed, width, nonempty, decoded, valid, rfl, rfl, rfl⟩, ?_⟩
  obtain ⟨_, hbase, _⟩ := RawCtxSourceOpen.sourceRecord_spec _ slices parsed
  have combined := RawCtxSourceOpen.baseOpen_combined c (absMaterial material).1 (absMaterial material).2
    (absBytes candidate.associated_data) (RawCtxSourceOpen.sourceRecord _ slices parsed).body
    (RawCtxSourceOpen.sourceRecord _ slices parsed).tag (RawCtxSourceOpen.sourceRecord _ slices parsed).tagLength
  rw [← hbase] at combined
  exact combined.symm.trans hplain.symm

/-- The post-root tail under any interpreter runs the initial KDF request, the deferred application getter and the local-owner raw receive, in that order, before the `afterOpening` gate. -/
theorem afterRoot_run {Response σ ι Result : Type} {base : OracleSpec ι}
    (handler : QueryImpl (PqxdhBeaconPhase2Publication.TailSpec Response) (StateT σ (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (prepared : PqxdhBeaconPhase2Preparation.Prepared Response)
    (root : PqxdhBeaconPhase2Preparation.Word32) (auxiliary : σ)
    (next : Option Staged × σ → OracleComp base Result) :
    (simulateQ handler (PqxdhBeaconPhase2Publication.afterRoot decode prepared root)).run auxiliary >>= next =
      (handler (.inr (.initial (PqxdhInitialRatchetComplementarity.beaconPending root).request))).run auxiliary >>=
        fun initial =>
        (handler (.inr (.application prepared.response))).run initial.2 >>= fun application =>
          match application.1 with
          | none => next (none, application.2)
          | some raw =>
              RawCtxWholeOwner.rawGame (fun query => handler (.inl query)) decode raw
                (localOwner (clearedCandidate prepared.candidate)
                  (PqxdhBeaconPhase2Publication.normalInitial
                    (PqxdhInitialRatchetComplementarity.beaconPending root) initial.1))
                application.2 >>= fun received =>
                next (afterOpening (clearedCandidate prepared.candidate) received.1.2.owner.kernel received.1.1,
                  received.2) := by
  simp only [PqxdhBeaconPhase2Publication.afterRoot, PqxdhBeaconPhase2Publication.initialRun, simulateQ_bind,
    simulateQ_spec_query, StateT.run_bind, bind_assoc, pure_bind]
  apply bind_congr
  intro initial
  apply bind_congr
  intro application
  cases application.1 with
  | none => simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  | some raw =>
      simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
      have adapter : handler ∘ₛ (PqxdhBeaconPhase2Publication.rawLift (Response := Response)) =
          fun query => handler (.inl query) := by
        funext query
        exact simulateQ_spec_query handler (.inl query)
      rw [← QueryImpl.simulateQ_compose, adapter]
      rfl

/-- Inside the Beacon's post-root tail, under any interpreter whose raw branch is a native interpreter with the ordinary AEAD branch, every staged success comes from this execution: an initial KDF reply at the Beacon's initial request installs the kernel `normalInitial (beaconPending root) initial`; the application getter returns the delivery `raw`; the local-owner raw receive of `raw` on that kernel has a present reply whose `afterOpening` is the staged result, with the receive's final kernel and primitive state; and that reply has a kernel opening at the installed kernel that ends in the receive's final primitive state. -/
theorem afterRoot_opening {Response σ ι : Type} {base : OracleSpec ι} (c : Pqxdh.Crypto)
    (handler : QueryImpl (PqxdhBeaconPhase2Publication.TailSpec Response) (StateT σ (OracleComp base)))
    (impl : QueryImpl RawCtxSourceOpen.NativeSpec (StateT σ (OracleComp base)))
    (routed : ∀ query, handler (.inl query) = (impl ∘ₛ RawCtxSourceOpen.nativeAdapter) query)
    (ordinary : OrdinaryOpen c impl)
    (decode : RawCtxReceive.FrameDecoder) (prepared : PqxdhBeaconPhase2Preparation.Prepared Response)
    (root : PqxdhBeaconPhase2Preparation.Word32) (auxiliary final : σ) (staged : Staged)
    (supported : (some staged, final) ∈ support
      ((simulateQ handler (PqxdhBeaconPhase2Publication.afterRoot decode prepared root)).run auxiliary)) :
    ∃ (initial : pqxdh.concrete.InitialRatchetKdfResponse) (initialState : σ) (raw : Pqxdh.Bytes) (application : σ)
      (received : (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxWholeOwner.OwnerState Unit) × σ)
      (input : RawCtxWholeOwner.OpenInput) (slices : RawCtxFrameDecoding.Slices)
      (parsed : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices)
      (width : input.context.associatedData.length = 281),
      (initial, initialState) ∈ support ((handler
        (.inr (.initial (PqxdhInitialRatchetComplementarity.beaconPending root).request))).run auxiliary) ∧
      (some raw, application) ∈ support ((handler (.inr (.application prepared.response))).run initialState) ∧
      received ∈ support (RawCtxWholeOwner.rawGame (impl ∘ₛ RawCtxSourceOpen.nativeAdapter) decode raw
        (localOwner (clearedCandidate prepared.candidate)
          (PqxdhBeaconPhase2Publication.normalInitial (PqxdhInitialRatchetComplementarity.beaconPending root)
            initial)) application) ∧
      received.2 = final ∧ received.1.1 = .Some staged.opened ∧
      afterOpening (clearedCandidate prepared.candidate) received.1.2.owner.kernel received.1.1 = some staged ∧
      KernelOpening c impl decode raw (clearedCandidate prepared.candidate)
        (PqxdhBeaconPhase2Publication.normalInitial (PqxdhInitialRatchetComplementarity.beaconPending root) initial)
        application received.2 staged.opened input slices parsed width := by
  have equation := afterRoot_run handler decode prepared root auxiliary (fun result => pure result)
  simp only [bind_pure] at equation
  rw [equation, mem_support_bind_iff] at supported
  obtain ⟨⟨initial, initialState⟩, initialSupport, supported⟩ := supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨⟨application, appState⟩, appSupport, supported⟩ := supported
  cases application with
  | none =>
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, Option.some_ne_none, false_and] at supported
  | some raw =>
      rw [mem_support_bind_iff] at supported
      obtain ⟨received, rawSupport, supported⟩ := supported
      rw [support_pure, Set.mem_singleton_iff] at supported
      have staging : afterOpening (clearedCandidate prepared.candidate) received.1.2.owner.kernel received.1.1 =
          some staged := (congrArg Prod.fst supported).symm
      have handlers : (fun query => handler (.inl query)) = impl ∘ₛ RawCtxSourceOpen.nativeAdapter :=
        funext routed
      rw [handlers] at rawSupport
      have reply := (authenticated_binding _ _ _ staged staging).1
      obtain ⟨input, slices, parsed, width, opening⟩ :=
        local_opening c impl ordinary decode raw (clearedCandidate prepared.candidate) _ appState received
          rawSupport staged.opened reply
      exact ⟨initial, initialState, raw, appState, received, input, slices, parsed, width, initialSupport, appSupport,
        rawSupport, (congrArg Prod.snd supported).symm, reply, staging, opening⟩

/-- The same kernel-level provenance for the related-root consumer's post-root tail, which the executable Phase 2 stage runs, under a native tail interpreter `native` whose raw branch has the ordinary AEAD branch: the initial KDF and application getter replies come from `native`'s auxiliary branch, and the staged result is the `afterOpening` of a local-owner receive on the installed initial kernel whose kernel opening ends in that receive's final primitive state. -/
theorem consumer_opening {Response σ ι : Type} {base : OracleSpec ι} (c : Pqxdh.Crypto)
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) (StateT σ (OracleComp base)))
    (ordinary : OrdinaryOpen c (fun query => native (.inl query)))
    (decode : RawCtxReceive.FrameDecoder) (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (root : PqxdhBeaconPhase2Preparation.Word32) (auxiliary final : σ) (staged : Staged)
    (supported : (some staged, final) ∈ support
      ((simulateQ native (PqxdhPhase2DhRootConsumer.afterRoot decode pending root)).run auxiliary)) :
    ∃ (initial : pqxdh.concrete.InitialRatchetKdfResponse) (initialState : σ) (raw : Pqxdh.Bytes) (application : σ)
      (received : (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxWholeOwner.OwnerState Unit) × σ)
      (input : RawCtxWholeOwner.OpenInput) (slices : RawCtxFrameDecoding.Slices)
      (parsed : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices)
      (width : input.context.associatedData.length = 281),
      (initial, initialState) ∈ support ((native
        (.inr (.initial (PqxdhInitialRatchetComplementarity.beaconPending root).request))).run auxiliary) ∧
      (some raw, application) ∈ support
        ((native (.inr (.application (PqxdhPhase2DhRootConsumer.cleared pending).response))).run initialState) ∧
      received ∈ support (RawCtxWholeOwner.rawGame
        ((fun query => native (.inl query)) ∘ₛ RawCtxSourceOpen.nativeAdapter) decode raw
        (localOwner (clearedCandidate (PqxdhPhase2DhRootConsumer.cleared pending).candidate)
          (PqxdhBeaconPhase2Publication.normalInitial (PqxdhInitialRatchetComplementarity.beaconPending root)
            initial)) application) ∧
      received.2 = final ∧ received.1.1 = .Some staged.opened ∧
      afterOpening (clearedCandidate (PqxdhPhase2DhRootConsumer.cleared pending).candidate)
        received.1.2.owner.kernel received.1.1 = some staged ∧
      KernelOpening c (fun query => native (.inl query)) decode raw
        (clearedCandidate (PqxdhPhase2DhRootConsumer.cleared pending).candidate)
        (PqxdhBeaconPhase2Publication.normalInitial (PqxdhInitialRatchetComplementarity.beaconPending root) initial)
        application received.2 staged.opened input slices parsed width := by
  unfold PqxdhPhase2DhRootConsumer.afterRoot at supported
  rw [← QueryImpl.simulateQ_compose] at supported
  have lift : native ∘ₛ (PqxdhBeaconPhase2Publication.nativeRawLift (Response := Response)) =
      fun query => native (.inl query) := by
    funext query
    exact simulateQ_spec_query native (.inl query)
  have routed : ∀ query, (native ∘ₛ PqxdhBeaconPhase2Publication.nativeTailAdapter) (.inl query) =
      ((fun query => native (.inl query)) ∘ₛ RawCtxSourceOpen.nativeAdapter) query := by
    intro query
    simp only [QueryImpl.apply_compose, PqxdhBeaconPhase2Publication.nativeTailAdapter]
    rw [← QueryImpl.simulateQ_compose, lift]
  have getter : ∀ query, (native ∘ₛ PqxdhBeaconPhase2Publication.nativeTailAdapter) (.inr query) =
      native (.inr query) := fun query => simulateQ_spec_query native (.inr query)
  obtain ⟨initial, initialState, raw, application, received, input, slices, parsed, width, initialSupport,
    appSupport, rawSupport, hfinal, reply, staging, opening⟩ :=
    afterRoot_opening c _ _ routed ordinary decode _ root auxiliary final staged supported
  rw [getter] at initialSupport appSupport
  exact ⟨initial, initialState, raw, application, received, input, slices, parsed, width, initialSupport, appSupport,
    rawSupport, hfinal, reply, staging, opening⟩

/-- Acceptance for the executable Phase 2 post-root tail: every staged success of the related-root consumer's tail, under a native interpreter with the ordinary AEAD branch, comes from a run whose initial KDF reply installs the kernel, whose getter returns the delivery, and whose local-owner receive on that kernel stages the result with a kernel opening ending in the receive's final state. The key the run opened with is therefore the source key of that opening's input, the key half of material reached from the installed kernel, and any correct seal under that key with the same full CTX tuple as the selected target, recording a key-ID-bound seal context, forces the accepted fields to be that context's sealed fields. It does not identify that material with any Server session's key. -/
theorem consumer_matching {Response σ ι : Type} {base : OracleSpec ι} (c : Pqxdh.Crypto)
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) (StateT σ (OracleComp base)))
    (ordinary : OrdinaryOpen c (fun query => native (.inl query)))
    (decode : RawCtxReceive.FrameDecoder) (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (root : PqxdhBeaconPhase2Preparation.Word32) (auxiliary final : σ) (staged : Staged)
    (supported : (some staged, final) ∈ support
      ((simulateQ native (PqxdhPhase2DhRootConsumer.afterRoot decode pending root)).run auxiliary)) :
    ∃ (initial : pqxdh.concrete.InitialRatchetKdfResponse) (initialState : σ) (raw : Pqxdh.Bytes) (application : σ)
      (received : (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxWholeOwner.OwnerState Unit) × σ)
      (input : RawCtxWholeOwner.OpenInput) (slices : RawCtxFrameDecoding.Slices)
      (parsed : RawCtxFrameDecoding.fromPayload input.context.frame.payload = some slices)
      (width : input.context.associatedData.length = 281),
      (initial, initialState) ∈ support ((native
        (.inr (.initial (PqxdhInitialRatchetComplementarity.beaconPending root).request))).run auxiliary) ∧
      (some raw, application) ∈ support
        ((native (.inr (.application (PqxdhPhase2DhRootConsumer.cleared pending).response))).run initialState) ∧
      received ∈ support (RawCtxWholeOwner.rawGame
        ((fun query => native (.inl query)) ∘ₛ RawCtxSourceOpen.nativeAdapter) decode raw
        (localOwner (clearedCandidate (PqxdhPhase2DhRootConsumer.cleared pending).candidate)
          (PqxdhBeaconPhase2Publication.normalInitial (PqxdhInitialRatchetComplementarity.beaconPending root)
            initial)) application) ∧
      received.2 = final ∧ received.1.1 = .Some staged.opened ∧
      afterOpening (clearedCandidate (PqxdhPhase2DhRootConsumer.cleared pending).candidate)
        received.1.2.owner.kernel received.1.1 = some staged ∧
      KernelOpening c (fun query => native (.inl query)) decode raw
        (clearedCandidate (PqxdhPhase2DhRootConsumer.cleared pending).candidate)
        (PqxdhBeaconPhase2Publication.normalInitial (PqxdhInitialRatchetComplementarity.beaconPending root) initial)
        application received.2 staged.opened input slices parsed width ∧
      ∀ entry, SealCorrect c (RawCtxSourceOpen.sourceKey input) entry →
        (RawCtxCanonicalOpening.selectedTarget input slices parsed width).toLegacy.sameFullTupleAsSuccessfulSeal entry →
        ∀ context, Records entry context → KeyIdBound context → acceptedFields staged = sealedFields context := by
  obtain ⟨initial, initialState, raw, application, received, input, slices, parsed, width, initialSupport,
    appSupport, rawSupport, hfinal, reply, staging, opening⟩ :=
    consumer_opening c native ordinary decode pending root auxiliary final staged supported
  have facts := opening
  obtain ⟨_, _, _, _, delivery, opens⟩ := facts
  exact ⟨initial, initialState, raw, application, received, input, slices, parsed, width, initialSupport,
    appSupport, rawSupport, hfinal, reply, staging, opening,
    fun entry correct same context records bound =>
      (accepted_of_match c _ _ _ _ staged staging decode raw _ delivery opens entry correct
        same context records bound).1⟩

end BeaconcryptCore.Computational.PqxdhPhase2LocalMatching

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.firstContext_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.firstContext_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.authenticated_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.authenticated_binding

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.accepted_of_plaintext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.accepted_of_plaintext

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.finish_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.finish_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.afterOpening_of_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.afterOpening_of_binding

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.relay_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.relay_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.historyCorrect_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.historyCorrect_iff

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.opens_of_targetOpen' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.opens_of_targetOpen

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.ctxSeal_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.ctxSeal_correct

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.target_matching' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.target_matching

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.localTarget_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.localTarget_context

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.matching_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.matching_open

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.sourceInput_records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.sourceInput_records

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.accepted_of_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.accepted_of_match

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.fresh_of_differs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.fresh_of_differs

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.fresh_forall' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.fresh_forall

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.attempt_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.attempt_accepted

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.won_of_attempt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.won_of_attempt

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.joint

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.native_ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.native_ordinary

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.reaches_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.reaches_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.reaches_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.reaches_scope

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.reaches_of_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.reaches_of_supported

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.raw_reaches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.raw_reaches

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.raw_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.raw_nonempty

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.sourceKey_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.sourceKey_material

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.local_opening' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.local_opening

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.afterRoot_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.afterRoot_run

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.afterRoot_opening' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.afterRoot_opening

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.consumer_opening' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.consumer_opening

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.consumer_matching' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2LocalMatching.consumer_matching

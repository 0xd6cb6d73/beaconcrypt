import BeaconcryptCore.Refinement.RepresentationBridge
import BeaconcryptCore.Refinement.RatchetReceiveStructural
import BeaconcryptCore.Refinement.RatchetReceiveRollback
import BeaconcryptCore.Computational.CtxRetainedTagProjection

/-!
# Raw-input CTX receive boundary

An adversary supplies only bytes. A separately implemented decoder either rejects or returns the exact sender, sequence, and protected payload. The wrapper validates the sender, nonempty body, and session-AD width, then runs the extracted receive driver with a fixed CTX interpreter on the actual request material and sequence. Acceptance returns the recovered plaintext; it never asks the adversary to guess it.

The decoder remains an explicit external parameter: this module does not formalize Cap'n Proto or assert that the Rust parser implements it. The cryptographic functions are likewise the byte-model operations, not an extraction of libsodium. Theorems connect this explicitly delimited wrapper to extracted state transitions, field provenance, commitment/base-AEAD acceptance, rollback, and replay. They do not lift the existing claimed-plaintext one-key advantage bound to this broader endpoint.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet.concrete
open BeaconcryptCore.Refinement.RepresentationBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BeaconcryptCore.Computational.RawCtxReceive

/-- The external decoder's exact fields; wire integers already have the Cap'n Proto width. -/
structure DecodedFrame where
  sequence : Std.U64
  sender : Std.U64
  payload : Pqxdh.Bytes

/-- External parser interface; exact single-frame consumption and traversal limits remain Rust correspondence obligations. -/
abbrev FrameDecoder := Pqxdh.Bytes → Option DecodedFrame

/-- Session AD is supplied by the selected established peer, not by the frame. -/
structure OpenContext where
  frame : DecodedFrame
  associatedData : Pqxdh.Bytes

/-- Runtime checks, including the production exclusion of an empty encrypted body. -/
def ValidFrame (expected : Std.U64) (ad : Pqxdh.Bytes) (frame : DecodedFrame) : Prop :=
  frame.sender = expected ∧ 80 < frame.payload.length ∧ ad.length = 153

instance (expected : Std.U64) (ad : Pqxdh.Bytes) (frame : DecodedFrame) :
    Decidable (ValidFrame expected ad frame) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The same request supplies key/nonce, sequence, payload, sender, and session AD to the CTX open operation. -/
def ctxOpen (c : Pqxdh.Crypto) (material : ratchet.RatchetMaterial)
    (sequence : Std.U64) (context : OpenContext) : core.option.Option Pqxdh.Bytes :=
  match Pqxdh.openRecord c (absMaterial material)
      ⟨context.associatedData, sequence.val, context.frame.sender.val⟩ context.frame.payload with
  | some plaintext => .Some plaintext
  | none => .None

/-- Execute the actual extracted getters before the fixed CTX interpreter. -/
def ctxOpenReply (c : Pqxdh.Crypto) : ReceiveOpen OpenContext → core.option.Option Pqxdh.Bytes :=
  receiveMaterialOpenReply (ctxOpen c)

/-- Arbitrary raw input is decoded and validated before entry-state ownership reaches the driver. -/
def rawReceive (decode : FrameDecoder) (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (expected : Std.U64) (ad raw : Pqxdh.Bytes) (entry : ConcreteRatchetKernel) :
    RustM (ConcreteRatchetKernel × core.option.Option Pqxdh.Bytes) :=
  match decode raw with
  | none => ok (entry, .None)
  | some frame =>
      if ValidFrame expected ad frame then
        receiveNext execute entry frame.sequence ⟨frame, ad⟩ (ctxOpenReply c)
      else ok (entry, .None)

/-- Prepared requests retain the exact admitted context and target sequence. -/
theorem prepared_fields (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (entry : ConcreteRatchetKernel) (context : OpenContext) (target : Std.U64)
    (opened : ReceiveOpen OpenContext)
    (h : PreparedReceiveRefines (concreteCrypto c execute) entry context target opened) :
    opened.context = context ∧ opened.sequence = ok target := by
  rcases h with ⟨prepared, hentry, hcontext, hphase, hfacts⟩ | ⟨pending, hentry, hcontext, hphase, hfacts⟩
  · exact ⟨hcontext, by simp [ReceiveOpen.sequence, hphase, hfacts.sequence_eq]⟩
  · exact ⟨hcontext, by simp [ReceiveOpen.sequence, hphase, hfacts.targetSequence]⟩

/-- The callback's accepted value is the decryption result, without an adversarial plaintext field. -/
theorem ctxOpen_success (c : Pqxdh.Crypto) (material : ratchet.RatchetMaterial)
    (sequence : Std.U64) (context : OpenContext) (plaintext : Pqxdh.Bytes)
    (h : ctxOpen c material sequence context = .Some plaintext) :
    Pqxdh.openRecord c (absMaterial material)
      ⟨context.associatedData, sequence.val, context.frame.sender.val⟩ context.frame.payload =
        some plaintext := by
  unfold ctxOpen at h
  split at h
  all_goals simp_all

/-- A raw acceptance exposes the parsed frame, the checked fields, and the exact extracted driver result. -/
theorem rawReceive_success_driver (decode : FrameDecoder) (c : Pqxdh.Crypto)
    (execute : KdfInterpreter) (expected : Std.U64) (ad raw plaintext : Pqxdh.Bytes)
    (entry result : ConcreteRatchetKernel)
    (h : rawReceive decode c execute expected ad raw entry = ok (result, .Some plaintext)) :
    ∃ frame, decode raw = some frame ∧ ValidFrame expected ad frame ∧
      receiveNext execute entry frame.sequence ⟨frame, ad⟩ (ctxOpenReply c) =
        ok (result, .Some plaintext) := by
  cases hd : decode raw <;> simp only [rawReceive, hd] at h
  · cases h
  · split at h
    all_goals simp_all

/-- Accepted callback output uses material and sequence read from the request itself. -/
theorem ctxOpenReply_success (c : Pqxdh.Crypto) (opened : ReceiveOpen OpenContext)
    (plaintext : Pqxdh.Bytes) (h : ctxOpenReply c opened = .Some plaintext) :
    ∃ material sequence, opened.material = ok (.Some material) ∧ opened.sequence = ok sequence ∧
      Pqxdh.openRecord c (absMaterial material)
        ⟨opened.context.associatedData, sequence.val, opened.context.frame.sender.val⟩
        opened.context.frame.payload = some plaintext := by
  unfold ctxOpenReply receiveMaterialOpenReply at h
  split at h
  · exact ⟨_, _, by assumption, by assumption, ctxOpen_success c _ _ _ plaintext h⟩
  · cases h

/-- Driver acceptance retains the actual request, its material getter, admitted fields, and exact publication result. -/
theorem driver_success_request (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (entry result : ConcreteRatchetKernel) (frame : DecodedFrame) (ad plaintext : Pqxdh.Bytes)
    (hvalid : ratchet.refined.ValidRefined entry.refined)
    (hrun : receiveNext execute entry frame.sequence ⟨frame, ad⟩ (ctxOpenReply c) =
      ok (result, .Some plaintext)) :
    ∃ (opened : ReceiveOpen OpenContext) (material : ratchet.RatchetMaterial),
      PreparedReceiveRefines (concreteCrypto c execute) entry ⟨frame, ad⟩ frame.sequence opened ∧
      opened.material = ok (.Some material) ∧ opened.context = ⟨frame, ad⟩ ∧
      opened.sequence = ok frame.sequence ∧
      Pqxdh.openRecord c (absMaterial material)
        ⟨ad, frame.sequence.val, frame.sender.val⟩ frame.payload = some plaintext ∧
      opened.finish (.Some plaintext) = ok (result, .Some plaintext) := by
  obtain ⟨_, effect, opened, count, hbegin, htrace, hprepared, hreply, hfinish⟩ :=
    receiveNext_successful_receive (recordCrypto c) execute entry frame.sequence
      ⟨frame, ad⟩ (ctxOpenReply c) hvalid result plaintext hrun
  obtain ⟨hcontext, hsequence⟩ := prepared_fields c execute entry ⟨frame, ad⟩ frame.sequence opened hprepared
  obtain ⟨material, sequence, hmaterial, hseq, hopen⟩ := ctxOpenReply_success c opened plaintext hreply
  have hseqeq : sequence = frame.sequence := RustM.ok.inj (hseq.symm.trans hsequence)
  exact ⟨opened, material, hprepared, hmaterial, hcontext, hsequence,
    by simpa only [hcontext, hseqeq] using hopen, hfinish⟩

/-- Protocol widths follow from the extracted material, decoded machine integers, and the runtime AD check. -/
theorem validated_record_wf (material : ratchet.RatchetMaterial) (frame : DecodedFrame)
    (expected : Std.U64) (ad : Pqxdh.Bytes) (h : ValidFrame expected ad frame) :
    Pqxdh.RecordWf (absMaterial material) ⟨ad, frame.sequence.val, frame.sender.val⟩ :=
  ⟨by simp [absMaterial], by simp [absMaterial], h.2.2, by scalar_tac, by scalar_tac⟩

/-- Raw acceptance entails modeled CTX/base-AEAD acceptance of the same bytes and consumption of the selected key. -/
theorem rawReceive_success (decode : FrameDecoder) (c : Pqxdh.Crypto)
    (execute : KdfInterpreter) (expected : Std.U64) (ad raw plaintext : Pqxdh.Bytes)
    (entry result : ConcreteRatchetKernel) (hvalid : ratchet.refined.ValidRefined entry.refined)
    (h : rawReceive decode c execute expected ad raw entry = ok (result, .Some plaintext)) :
    ∃ (frame : DecodedFrame) (opened : ReceiveOpen OpenContext)
      (material : ratchet.RatchetMaterial) (record : Pqxdh.RecordCipher), decode raw = some frame ∧ ValidFrame expected ad frame ∧
      PreparedReceiveRefines (concreteCrypto c execute) entry ⟨frame, ad⟩ frame.sequence opened ∧
      opened.material = ok (.Some material) ∧ opened.context = ⟨frame, ad⟩ ∧
      opened.sequence = ok frame.sequence ∧
      Pqxdh.RecordWf (absMaterial material) ⟨ad, frame.sequence.val, frame.sender.val⟩ ∧
      Pqxdh.decodeRecord frame.payload = some record ∧ record.encode = frame.payload ∧
      record.commit = Pqxdh.ctxCommit c (absMaterial material)
        ⟨ad, frame.sequence.val, frame.sender.val⟩ record.tag ∧
      c.aeadOpen (absMaterial material).1 (absMaterial material).2 ad record.body record.tag =
        some plaintext ∧ ReceiveSuccess frame.sequence result := by
  obtain ⟨frame, hd, hv, hrun⟩ := rawReceive_success_driver decode c execute expected ad raw plaintext entry result h
  obtain ⟨opened, material, hprepared, hmaterial, hcontext, hsequence, hopen, _⟩ :=
    driver_success_request c execute entry result frame ad plaintext hvalid hrun
  obtain ⟨record, hdecode, hcommit, hbase⟩ := CtxRetainedTagProjection.openRecord_success_implies_base_success c hopen
  exact ⟨frame, opened, material, record, hd, hv, hprepared, hmaterial, hcontext, hsequence,
    validated_record_wf material frame expected ad hv,
    hdecode, CtxRetainedTagProjection.encode_eq_of_decodeRecord_eq_some hdecode, hcommit, hbase,
    receiveNext_success (recordCrypto c) execute entry frame.sequence ⟨frame, ad⟩
      (ctxOpenReply c) hvalid result plaintext hrun⟩

/-- Every raw rejection preserves the complete entry kernel, including malformed and authentication-failing inputs. -/
theorem rawReceive_failure_entry (decode : FrameDecoder) (c : Pqxdh.Crypto)
    (execute : KdfInterpreter) (expected : Std.U64) (ad raw : Pqxdh.Bytes)
    (entry result : ConcreteRatchetKernel)
    (h : rawReceive decode c execute expected ad raw entry = ok (result, .None)) :
    result = entry := by
  cases hd : decode raw <;> simp only [rawReceive, hd] at h
  · exact (congrArg Prod.fst (RustM.ok.inj h)).symm
  · split at h
    · exact receiveNext_failure_entry execute entry result _ _ (ctxOpenReply c) h
    · exact (congrArg Prod.fst (RustM.ok.inj h)).symm

/-- A successfully accepted raw frame cannot be delivered twice; replay leaves the poststate unchanged. -/
theorem rawReceive_success_replay (decode : FrameDecoder) (c : Pqxdh.Crypto)
    (execute : KdfInterpreter) (expected : Std.U64) (ad raw plaintext : Pqxdh.Bytes)
    (entry result : ConcreteRatchetKernel) (hvalid : ratchet.refined.ValidRefined entry.refined)
    (h : rawReceive decode c execute expected ad raw entry = ok (result, .Some plaintext)) :
    rawReceive decode c execute expected ad raw result = ok (result, .None) := by
  obtain ⟨frame, hd, hv, hrun⟩ := rawReceive_success_driver decode c execute expected ad raw plaintext entry result h
  simpa only [rawReceive, hd, if_pos hv] using
    receiveNext_success_replay (recordCrypto c) execute execute entry frame.sequence
      ⟨frame, ad⟩ (ctxOpenReply c) hvalid result plaintext hrun ⟨frame, ad⟩ (ctxOpenReply c)

/-- The delimited pure-decoder wrapper always returns a kernel and an optional actual plaintext. -/
theorem rawReceive_total (decode : FrameDecoder) (c : Pqxdh.Crypto)
    (execute : KdfInterpreter) (expected : Std.U64) (ad raw : Pqxdh.Bytes)
    (entry : ConcreteRatchetKernel) :
    ∃ result output, rawReceive decode c execute expected ad raw entry = ok (result, output) := by
  unfold rawReceive
  split
  · exact ⟨entry, .None, rfl⟩
  · split
    · exact receiveNext_total execute entry _ _ (ctxOpenReply c)
    · exact ⟨entry, .None, rfl⟩

end BeaconcryptCore.Computational.RawCtxReceive

import BeaconcryptCore.Refinement.PqxdhCore
import BeaconcryptCore.Model.Pqxdh.Commit

/-!
# PQXDH commitment refinement

This module connects the current Hax-extracted commitment helpers to the ideal
PQXDH commitment representation.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Result
open beaconcrypt_core

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PqxdhRefinement

/-- The commitment and registration helpers use the same extracted little-endian
encoding implementation. -/
theorem commitment_encode_u64_le_eq_registration (x : Std.U64) :
    commitment.encode_u64_le x =
      pqxdh.registration_key_id_binding x >>= fun b => ok b.bytes := by
  rfl

/-- **Extracted commitment integer refinement.** The eight bytes returned by the
current extracted commitment helper are exactly the ideal `Pqxdh.LE64` encoding. -/
theorem commitment_encode_u64_le_abs (x : Std.U64) :
    ∃ bytes : Std.Array Std.U8 8#usize,
      commitment.encode_u64_le x = ok bytes ∧
        absBytes bytes = Pqxdh.LE64 x.val := by
  obtain ⟨binding, hbinding, habs⟩ := registration_key_id_binding_abs x
  refine ⟨binding.bytes, ?_, habs⟩
  rw [commitment_encode_u64_le_eq_registration, hbinding]
  rfl

/-! ## Complete commitment transcript -/

/-- The generated closure selects each byte from the six transcript regions at the
production offsets. -/
theorem build_commitment_transcript_call_mut
    (key : Std.Array Std.U8 32#usize)
    (nonce : Std.Array Std.U8 12#usize)
    (associatedData : Std.Array Std.U8 153#usize)
    (tag : Std.Array Std.U8 16#usize)
    (sequenceBytes senderBytes : Std.Array Std.U8 8#usize)
    (index : Std.Usize) :
    commitment.build_commitment_transcript.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
        ((key, nonce, associatedData, tag, sequenceBytes, senderBytes) :
          commitment.build_commitment_transcript.closure) index =
      (if index < 32#usize then
          Std.Array.index_usize key index >>= fun byte =>
            ok (byte, ((key, nonce, associatedData, tag, sequenceBytes, senderBytes) :
              commitment.build_commitment_transcript.closure))
        else if index < 44#usize then
          index - 32#usize >>= fun offset => Std.Array.index_usize nonce offset >>= fun byte =>
            ok (byte, ((key, nonce, associatedData, tag, sequenceBytes, senderBytes) :
              commitment.build_commitment_transcript.closure))
        else if index < 197#usize then
          index - 44#usize >>= fun offset =>
            Std.Array.index_usize associatedData offset >>= fun byte =>
              ok (byte, ((key, nonce, associatedData, tag, sequenceBytes, senderBytes) :
                commitment.build_commitment_transcript.closure))
        else if index < 213#usize then
          index - 197#usize >>= fun offset => Std.Array.index_usize tag offset >>= fun byte =>
            ok (byte, ((key, nonce, associatedData, tag, sequenceBytes, senderBytes) :
              commitment.build_commitment_transcript.closure))
        else if index < 221#usize then
          index - 213#usize >>= fun offset =>
            Std.Array.index_usize sequenceBytes offset >>= fun byte =>
              ok (byte, ((key, nonce, associatedData, tag, sequenceBytes, senderBytes) :
                commitment.build_commitment_transcript.closure))
        else
          index - 221#usize >>= fun offset =>
            Std.Array.index_usize senderBytes offset >>= fun byte =>
              ok (byte, ((key, nonce, associatedData, tag, sequenceBytes, senderBytes) :
                commitment.build_commitment_transcript.closure))) := by
  rfl

/-- **Extracted commitment transcript refinement.** The current generated builder
returns exactly the ideal 229-byte CTX preimage in key, nonce, associated-data, tag,
sequence, and sender order. -/
theorem build_commitment_transcript_abs
    (key : Std.Array Std.U8 32#usize)
    (nonce : Std.Array Std.U8 12#usize)
    (associatedData : Std.Array Std.U8 153#usize)
    (tag : Std.Array Std.U8 16#usize)
    (sequence senderId : Std.U64) :
    ∃ transcript : commitment.CommitmentTranscript,
      commitment.build_commitment_transcript key nonce associatedData tag sequence senderId =
          ok transcript ∧
        absBytes transcript.bytes =
          Pqxdh.ctxPreimage (absBytes key, absBytes nonce)
            ⟨absBytes associatedData, sequence.val, senderId.val⟩ (absBytes tag) := by
  obtain ⟨sequenceBytes, hsequence, hsequenceAbs⟩ := commitment_encode_u64_le_abs sequence
  obtain ⟨senderBytes, hsender, hsenderAbs⟩ := commitment_encode_u64_le_abs senderId
  have hlen :
      (Pqxdh.ctxPreimage (absBytes key, absBytes nonce)
        ⟨absBytes associatedData, sequence.val, senderId.val⟩ (absBytes tag)).length =
          (229#usize).val := by
    simp [Pqxdh.ctxPreimage]
  have hcall : ∀ i, i < (229#usize).val →
      commitment.build_commitment_transcript.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
          ((key, nonce, associatedData, tag, sequenceBytes, senderBytes) :
            commitment.build_commitment_transcript.closure)
          ⟨BitVec.ofNat _ i⟩ =
        ok ((if i < 32 then key.val[i]!
          else if i < 44 then nonce.val[i - 32]!
          else if i < 197 then associatedData.val[i - 44]!
          else if i < 213 then tag.val[i - 197]!
          else if i < 221 then sequenceBytes.val[i - 213]!
          else senderBytes.val[i - 221]!),
          ((key, nonce, associatedData, tag, sequenceBytes, senderBytes) :
            commitment.build_commitment_transcript.closure)) := by
    intro i hi
    have hval : (⟨BitVec.ofNat _ i⟩ : Std.Usize).val = i := usize_mk_val i (by
      simp at hi
      omega)
    have hlt : ∀ k : Std.Usize, ((⟨BitVec.ofNat _ i⟩ : Std.Usize) < k) ↔ i < k.val := by
      intro k
      rw [Std.UScalar.lt_equiv, hval]
    have hi229 : i < 229 := by simpa using hi
    rw [build_commitment_transcript_call_mut]
    by_cases h32 : i < 32
    · rw [if_pos ((hlt 32#usize).mpr (by simpa using h32)),
          index_usize_eq key _ (by
            rw [hval]
            simp
            omega), hval]
      simp only [if_pos h32]
      rfl
    · by_cases h44 : i < 44
      · rw [if_neg (fun hc => h32 (by simpa using (hlt 32#usize).mp hc)),
          if_pos ((hlt 44#usize).mpr (by simpa using h44))]
        have hsub : (32#usize).val ≤ (⟨BitVec.ofNat _ i⟩ : Std.Usize).val := by
          rw [hval]
          simp
          omega
        rw [usize_sub_eq _ _ hsub]
        rw [show (⟨BitVec.ofNat _ i⟩ : Std.Usize).val - (32#usize).val = i - 32 by
          rw [hval]
          simp]
        have h1 : (⟨BitVec.ofNat _ (i - 32)⟩ : Std.Usize).val = i - 32 :=
          usize_mk_val (i - 32) (by omega)
        simp only [bind_tc_ok]
        rw [index_usize_eq nonce _ (by
          rw [h1]
          simp
          omega), h1]
        simp only [if_neg h32, if_pos h44]
        rfl
      · by_cases h197 : i < 197
        · rw [if_neg (fun hc => h32 (by simpa using (hlt 32#usize).mp hc)),
            if_neg (fun hc => h44 (by simpa using (hlt 44#usize).mp hc)),
            if_pos ((hlt 197#usize).mpr (by simpa using h197))]
          have hsub : (44#usize).val ≤ (⟨BitVec.ofNat _ i⟩ : Std.Usize).val := by
            rw [hval]
            simp
            omega
          rw [usize_sub_eq _ _ hsub]
          rw [show (⟨BitVec.ofNat _ i⟩ : Std.Usize).val - (44#usize).val = i - 44 by
            rw [hval]
            simp]
          have h1 : (⟨BitVec.ofNat _ (i - 44)⟩ : Std.Usize).val = i - 44 :=
            usize_mk_val (i - 44) (by omega)
          simp only [bind_tc_ok]
          rw [index_usize_eq associatedData _ (by
            rw [h1]
            simp
            omega), h1]
          simp only [if_neg h32, if_neg h44, if_pos h197]
          rfl
        · by_cases h213 : i < 213
          · rw [if_neg (fun hc => h32 (by simpa using (hlt 32#usize).mp hc)),
              if_neg (fun hc => h44 (by simpa using (hlt 44#usize).mp hc)),
              if_neg (fun hc => h197 (by simpa using (hlt 197#usize).mp hc)),
              if_pos ((hlt 213#usize).mpr (by simpa using h213))]
            have hsub : (197#usize).val ≤ (⟨BitVec.ofNat _ i⟩ : Std.Usize).val := by
              rw [hval]
              simp
              omega
            rw [usize_sub_eq _ _ hsub]
            rw [show (⟨BitVec.ofNat _ i⟩ : Std.Usize).val - (197#usize).val = i - 197 by
              rw [hval]
              simp]
            have h1 : (⟨BitVec.ofNat _ (i - 197)⟩ : Std.Usize).val = i - 197 :=
              usize_mk_val (i - 197) (by omega)
            simp only [bind_tc_ok]
            rw [index_usize_eq tag _ (by
              rw [h1]
              simp
              omega), h1]
            simp only [if_neg h32, if_neg h44, if_neg h197, if_pos h213]
            rfl
          · by_cases h221 : i < 221
            · rw [if_neg (fun hc => h32 (by simpa using (hlt 32#usize).mp hc)),
                if_neg (fun hc => h44 (by simpa using (hlt 44#usize).mp hc)),
                if_neg (fun hc => h197 (by simpa using (hlt 197#usize).mp hc)),
                if_neg (fun hc => h213 (by simpa using (hlt 213#usize).mp hc)),
                if_pos ((hlt 221#usize).mpr (by simpa using h221))]
              have hsub : (213#usize).val ≤ (⟨BitVec.ofNat _ i⟩ : Std.Usize).val := by
                rw [hval]
                simp
                omega
              rw [usize_sub_eq _ _ hsub]
              rw [show (⟨BitVec.ofNat _ i⟩ : Std.Usize).val - (213#usize).val = i - 213 by
                rw [hval]
                simp]
              have h1 : (⟨BitVec.ofNat _ (i - 213)⟩ : Std.Usize).val = i - 213 :=
                usize_mk_val (i - 213) (by omega)
              simp only [bind_tc_ok]
              rw [index_usize_eq sequenceBytes _ (by
                rw [h1]
                simp
                omega), h1]
              simp only [if_neg h32, if_neg h44, if_neg h197, if_neg h213, if_pos h221]
              rfl
            · rw [if_neg (fun hc => h32 (by simpa using (hlt 32#usize).mp hc)),
                if_neg (fun hc => h44 (by simpa using (hlt 44#usize).mp hc)),
                if_neg (fun hc => h197 (by simpa using (hlt 197#usize).mp hc)),
                if_neg (fun hc => h213 (by simpa using (hlt 213#usize).mp hc)),
                if_neg (fun hc => h221 (by simpa using (hlt 221#usize).mp hc))]
              have hsub : (221#usize).val ≤ (⟨BitVec.ofNat _ i⟩ : Std.Usize).val := by
                rw [hval]
                simp
                omega
              rw [usize_sub_eq _ _ hsub]
              rw [show (⟨BitVec.ofNat _ i⟩ : Std.Usize).val - (221#usize).val = i - 221 by
                rw [hval]
                simp]
              have h1 : (⟨BitVec.ofNat _ (i - 221)⟩ : Std.Usize).val = i - 221 :=
                usize_mk_val (i - 221) (by omega)
              simp only [bind_tc_ok]
              rw [index_usize_eq senderBytes _ (by
                rw [h1]
                simp
                omega), h1]
              simp only [if_neg h32, if_neg h44, if_neg h197, if_neg h213, if_neg h221]
              rfl
  have hbyte : ∀ i, i < (229#usize).val →
      absByte (if i < 32 then key.val[i]!
        else if i < 44 then nonce.val[i - 32]!
        else if i < 197 then associatedData.val[i - 44]!
        else if i < 213 then tag.val[i - 197]!
        else if i < 221 then sequenceBytes.val[i - 213]!
        else senderBytes.val[i - 221]!) =
      (Pqxdh.ctxPreimage (absBytes key, absBytes nonce)
        ⟨absBytes associatedData, sequence.val, senderId.val⟩ (absBytes tag))[i]! := by
    intro i hi
    have hi229 : i < 229 := by simpa using hi
    rw [Pqxdh.ctxPreimage,
      getElem!_append2 _ _ 221 (by simp),
      getElem!_append2 _ _ 213 (by simp),
      getElem!_append2 _ _ 197 (by simp),
      getElem!_append2 _ _ 44 (by simp),
      getElem!_append2 _ _ 32 (by simp)]
    by_cases h32 : i < 32
    · simp only [if_pos h32, if_pos (show i < 44 by omega),
        if_pos (show i < 197 by omega), if_pos (show i < 213 by omega),
        if_pos (show i < 221 by omega)]
      exact (absBytes_getElem! key i (by simp; omega)).symm
    · by_cases h44 : i < 44
      · simp only [if_neg h32, if_pos h44, if_pos (show i < 197 by omega),
          if_pos (show i < 213 by omega), if_pos (show i < 221 by omega)]
        exact (absBytes_getElem! nonce (i - 32) (by simp; omega)).symm
      · by_cases h197 : i < 197
        · simp only [if_neg h32, if_neg h44, if_pos h197,
            if_pos (show i < 213 by omega), if_pos (show i < 221 by omega)]
          exact (absBytes_getElem! associatedData (i - 44) (by simp; omega)).symm
        · by_cases h213 : i < 213
          · simp only [if_neg h32, if_neg h44, if_neg h197, if_pos h213,
              if_pos (show i < 221 by omega)]
            exact (absBytes_getElem! tag (i - 197) (by simp; omega)).symm
          · by_cases h221 : i < 221
            · simp only [if_neg h32, if_neg h44, if_neg h197, if_neg h213, if_pos h221]
              rw [← hsequenceAbs]
              exact (absBytes_getElem! sequenceBytes (i - 213) (by simp; omega)).symm
            · simp only [if_neg h32, if_neg h44, if_neg h197, if_neg h213, if_neg h221]
              rw [← hsenderAbs]
              exact (absBytes_getElem! senderBytes (i - 221) (by simp; omega)).symm
  obtain ⟨bytes, hfrom, habs⟩ :=
    from_fn_absBytes (F := commitment.build_commitment_transcript.closure) 229#usize
      commitment.build_commitment_transcript.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
      ((key, nonce, associatedData, tag, sequenceBytes, senderBytes) :
        commitment.build_commitment_transcript.closure) _ _ hlen hcall hbyte
  refine ⟨⟨bytes⟩, ?_, habs⟩
  unfold commitment.build_commitment_transcript
  rw [hsequence]
  simp only [bind_tc_ok]
  rw [hsender]
  simp only [bind_tc_ok]
  rw [hfrom]
  rfl

end PqxdhRefinement

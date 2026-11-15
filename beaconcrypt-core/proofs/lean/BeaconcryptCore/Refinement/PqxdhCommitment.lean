import BeaconcryptCore.Refinement.PqxdhCore
import BeaconcryptCore.Model.Pqxdh.Commit

/-!
# PQXDH commitment refinement

This module connects the current Hax-extracted commitment helpers to the ideal
PQXDH commitment representation.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
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
    (associatedData : Std.Array Std.U8 151#usize)
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
        else if index < 195#usize then
          index - 44#usize >>= fun offset =>
            Std.Array.index_usize associatedData offset >>= fun byte =>
              ok (byte, ((key, nonce, associatedData, tag, sequenceBytes, senderBytes) :
                commitment.build_commitment_transcript.closure))
        else if index < 211#usize then
          index - 195#usize >>= fun offset => Std.Array.index_usize tag offset >>= fun byte =>
            ok (byte, ((key, nonce, associatedData, tag, sequenceBytes, senderBytes) :
              commitment.build_commitment_transcript.closure))
        else if index < 219#usize then
          index - 211#usize >>= fun offset =>
            Std.Array.index_usize sequenceBytes offset >>= fun byte =>
              ok (byte, ((key, nonce, associatedData, tag, sequenceBytes, senderBytes) :
                commitment.build_commitment_transcript.closure))
        else
          index - 219#usize >>= fun offset =>
            Std.Array.index_usize senderBytes offset >>= fun byte =>
              ok (byte, ((key, nonce, associatedData, tag, sequenceBytes, senderBytes) :
                commitment.build_commitment_transcript.closure))) := by
  rfl

/-- **Extracted commitment transcript refinement.** The current generated builder
returns exactly the ideal 227-byte CTX preimage in key, nonce, associated-data, tag,
sequence, and sender order. -/
theorem build_commitment_transcript_abs
    (key : Std.Array Std.U8 32#usize)
    (nonce : Std.Array Std.U8 12#usize)
    (associatedData : Std.Array Std.U8 151#usize)
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
          (227#usize).val := by
    simp [Pqxdh.ctxPreimage]
  have hcall : ∀ i, i < (227#usize).val →
      commitment.build_commitment_transcript.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
          ((key, nonce, associatedData, tag, sequenceBytes, senderBytes) :
            commitment.build_commitment_transcript.closure)
          ⟨BitVec.ofNat _ i⟩ =
        ok ((if i < 32 then key.val[i]!
          else if i < 44 then nonce.val[i - 32]!
          else if i < 195 then associatedData.val[i - 44]!
          else if i < 211 then tag.val[i - 195]!
          else if i < 219 then sequenceBytes.val[i - 211]!
          else senderBytes.val[i - 219]!),
          ((key, nonce, associatedData, tag, sequenceBytes, senderBytes) :
            commitment.build_commitment_transcript.closure)) := by
    intro i hi
    have hval : (⟨BitVec.ofNat _ i⟩ : Std.Usize).val = i := usize_mk_val i (by
      simp at hi
      omega)
    have hlt : ∀ k : Std.Usize, ((⟨BitVec.ofNat _ i⟩ : Std.Usize) < k) ↔ i < k.val := by
      intro k
      rw [Std.UScalar.lt_equiv, hval]
    have hi227 : i < 227 := by simpa using hi
    rw [build_commitment_transcript_call_mut]
    by_cases h32 : i < 32
    · rw [ite_eq_left ((hlt 32#usize).mpr (by simpa using h32)),
          index_usize_eq key _ (by
            rw [hval]
            simp
            omega), hval]
      simp only [ite_eq_left h32]
      rfl
    · by_cases h44 : i < 44
      · rw [ite_eq_right (fun hc => h32 (by simpa using (hlt 32#usize).mp hc)),
          ite_eq_left ((hlt 44#usize).mpr (by simpa using h44))]
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
        simp only [ite_eq_right h32, ite_eq_left h44]
        rfl
      · by_cases h195 : i < 195
        · rw [ite_eq_right (fun hc => h32 (by simpa using (hlt 32#usize).mp hc)),
            ite_eq_right (fun hc => h44 (by simpa using (hlt 44#usize).mp hc)),
            ite_eq_left ((hlt 195#usize).mpr (by simpa using h195))]
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
          simp only [ite_eq_right h32, ite_eq_right h44, ite_eq_left h195]
          rfl
        · by_cases h211 : i < 211
          · rw [ite_eq_right (fun hc => h32 (by simpa using (hlt 32#usize).mp hc)),
              ite_eq_right (fun hc => h44 (by simpa using (hlt 44#usize).mp hc)),
              ite_eq_right (fun hc => h195 (by simpa using (hlt 195#usize).mp hc)),
              ite_eq_left ((hlt 211#usize).mpr (by simpa using h211))]
            have hsub : (195#usize).val ≤ (⟨BitVec.ofNat _ i⟩ : Std.Usize).val := by
              rw [hval]
              simp
              omega
            rw [usize_sub_eq _ _ hsub]
            rw [show (⟨BitVec.ofNat _ i⟩ : Std.Usize).val - (195#usize).val = i - 195 by
              rw [hval]
              simp]
            have h1 : (⟨BitVec.ofNat _ (i - 195)⟩ : Std.Usize).val = i - 195 :=
              usize_mk_val (i - 195) (by omega)
            simp only [bind_tc_ok]
            rw [index_usize_eq tag _ (by
              rw [h1]
              simp
              omega), h1]
            simp only [ite_eq_right h32, ite_eq_right h44, ite_eq_right h195, ite_eq_left h211]
            rfl
          · by_cases h219 : i < 219
            · rw [ite_eq_right (fun hc => h32 (by simpa using (hlt 32#usize).mp hc)),
                ite_eq_right (fun hc => h44 (by simpa using (hlt 44#usize).mp hc)),
                ite_eq_right (fun hc => h195 (by simpa using (hlt 195#usize).mp hc)),
                ite_eq_right (fun hc => h211 (by simpa using (hlt 211#usize).mp hc)),
                ite_eq_left ((hlt 219#usize).mpr (by simpa using h219))]
              have hsub : (211#usize).val ≤ (⟨BitVec.ofNat _ i⟩ : Std.Usize).val := by
                rw [hval]
                simp
                omega
              rw [usize_sub_eq _ _ hsub]
              rw [show (⟨BitVec.ofNat _ i⟩ : Std.Usize).val - (211#usize).val = i - 211 by
                rw [hval]
                simp]
              have h1 : (⟨BitVec.ofNat _ (i - 211)⟩ : Std.Usize).val = i - 211 :=
                usize_mk_val (i - 211) (by omega)
              simp only [bind_tc_ok]
              rw [index_usize_eq sequenceBytes _ (by
                rw [h1]
                simp
                omega), h1]
              simp only [ite_eq_right h32, ite_eq_right h44, ite_eq_right h195, ite_eq_right h211, ite_eq_left h219]
              rfl
            · rw [ite_eq_right (fun hc => h32 (by simpa using (hlt 32#usize).mp hc)),
                ite_eq_right (fun hc => h44 (by simpa using (hlt 44#usize).mp hc)),
                ite_eq_right (fun hc => h195 (by simpa using (hlt 195#usize).mp hc)),
                ite_eq_right (fun hc => h211 (by simpa using (hlt 211#usize).mp hc)),
                ite_eq_right (fun hc => h219 (by simpa using (hlt 219#usize).mp hc))]
              have hsub : (219#usize).val ≤ (⟨BitVec.ofNat _ i⟩ : Std.Usize).val := by
                rw [hval]
                simp
                omega
              rw [usize_sub_eq _ _ hsub]
              rw [show (⟨BitVec.ofNat _ i⟩ : Std.Usize).val - (219#usize).val = i - 219 by
                rw [hval]
                simp]
              have h1 : (⟨BitVec.ofNat _ (i - 219)⟩ : Std.Usize).val = i - 219 :=
                usize_mk_val (i - 219) (by omega)
              simp only [bind_tc_ok]
              rw [index_usize_eq senderBytes _ (by
                rw [h1]
                simp
                omega), h1]
              simp only [ite_eq_right h32, ite_eq_right h44, ite_eq_right h195, ite_eq_right h211, ite_eq_right h219]
              rfl
  have hbyte : ∀ i, i < (227#usize).val →
      absByte (if i < 32 then key.val[i]!
        else if i < 44 then nonce.val[i - 32]!
        else if i < 195 then associatedData.val[i - 44]!
        else if i < 211 then tag.val[i - 195]!
        else if i < 219 then sequenceBytes.val[i - 211]!
        else senderBytes.val[i - 219]!) =
      (Pqxdh.ctxPreimage (absBytes key, absBytes nonce)
        ⟨absBytes associatedData, sequence.val, senderId.val⟩ (absBytes tag))[i]! := by
    intro i hi
    have hi227 : i < 227 := by simpa using hi
    rw [Pqxdh.ctxPreimage,
      getElem!_append2 _ _ 219 (by simp),
      getElem!_append2 _ _ 211 (by simp),
      getElem!_append2 _ _ 195 (by simp),
      getElem!_append2 _ _ 44 (by simp),
      getElem!_append2 _ _ 32 (by simp)]
    by_cases h32 : i < 32
    · simp only [ite_eq_left h32, ite_eq_left (show i < 44 by omega),
        ite_eq_left (show i < 195 by omega), ite_eq_left (show i < 211 by omega),
        ite_eq_left (show i < 219 by omega)]
      exact (absBytes_getElem! key i (by simp; omega)).symm
    · by_cases h44 : i < 44
      · simp only [ite_eq_right h32, ite_eq_left h44, ite_eq_left (show i < 195 by omega),
          ite_eq_left (show i < 211 by omega), ite_eq_left (show i < 219 by omega)]
        exact (absBytes_getElem! nonce (i - 32) (by simp; omega)).symm
      · by_cases h195 : i < 195
        · simp only [ite_eq_right h32, ite_eq_right h44, ite_eq_left h195,
            ite_eq_left (show i < 211 by omega), ite_eq_left (show i < 219 by omega)]
          exact (absBytes_getElem! associatedData (i - 44) (by simp; omega)).symm
        · by_cases h211 : i < 211
          · simp only [ite_eq_right h32, ite_eq_right h44, ite_eq_right h195, ite_eq_left h211,
              ite_eq_left (show i < 219 by omega)]
            exact (absBytes_getElem! tag (i - 195) (by simp; omega)).symm
          · by_cases h219 : i < 219
            · simp only [ite_eq_right h32, ite_eq_right h44, ite_eq_right h195, ite_eq_right h211, ite_eq_left h219]
              rw [← hsequenceAbs]
              exact (absBytes_getElem! sequenceBytes (i - 211) (by simp; omega)).symm
            · simp only [ite_eq_right h32, ite_eq_right h44, ite_eq_right h195, ite_eq_right h211, ite_eq_right h219]
              rw [← hsenderAbs]
              exact (absBytes_getElem! senderBytes (i - 219) (by simp; omega)).symm
  obtain ⟨bytes, hfrom, habs⟩ :=
    from_fn_absBytes (F := commitment.build_commitment_transcript.closure) 227#usize
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

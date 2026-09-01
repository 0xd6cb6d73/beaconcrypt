import BeaconcryptCore.Refinement.PqxdhEncoding

/-!
# The generated PQXDH transcript builders refine the ideal ones

The ideal model fixes

* the registration identifier `RID = IK_B ‖ OT_B` (`Pqxdh.ValidInit.rid`, spec §6),
* the all-zero X25519 rejection value `Pqxdh.zero32` (spec §7),
* the PQXDH transcript `IKM_PQ = FF^32 ‖ DH₁ ‖ DH₂ ‖ DH₃ ‖ DH₄ ‖ SS`
  (`Pqxdh.pqxdhIKM`, spec §8),
* the associated data `AD = Tag_sig(IK_S) ‖ Tag_sig(IK_B) ‖ INFO_PQ ‖ INFO_R`
  (`Pqxdh.assocData`, spec §9),
* the little-endian key-identifier binding `LE64(kid)` (`Pqxdh.LE64`, spec §12).

This file proves that the corresponding generated routines compute exactly those
byte strings, and that the generated all-zero test decides the ideal one.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

open beaconcrypt_core

namespace PqxdhRefinement

/-! ## Generated size constants -/

theorem sign_public_key_size_eq : pqxdh.SIGN_PUBLIC_KEY_SIZE = 32#usize := by
  simp [pqxdh.SIGN_PUBLIC_KEY_SIZE]

theorem dh_secret_size_eq : pqxdh.DH_SECRET_SIZE = 32#usize := by
  simp [pqxdh.DH_SECRET_SIZE]

theorem pqxdh_padding_size_eq : pqxdh.PQXDH_PADDING_SIZE = 32#usize := by
  simp [pqxdh.PQXDH_PADDING_SIZE]

/-! ## Indexing concatenations -/

theorem getElem!_append2 (a b : Pqxdh.Bytes) (na : ℕ) (ha : a.length = na) (i : ℕ) :
    (a ++ b)[i]! = if i < na then a[i]! else b[i - na]! := by
  rw [getElem!_append, ha]

/-! ## The all-zero test -/

@[simp] theorem absBytes_zero32 :
    absBytes (Std.Array.repeat 32#usize 0#u8) = Pqxdh.zero32 := by
  simp [absBytes, Std.Array.repeat, Pqxdh.zero32, absByte]

/-- The generated all-zero test decides the ideal rejection condition of spec §7. -/
theorem is_all_zero_abs (bytes : Std.Array Std.U8 32#usize) :
    pqxdh.is_all_zero bytes = ok (decide (absBytes bytes = Pqxdh.zero32)) := by
  unfold pqxdh.is_all_zero
  rw [array_eq_abs]
  simp

/-! ## The registration identifier -/

/-- The generated registration identifier is the ideal `RID = IK_B ‖ OT_B`. -/
theorem registration_id_abs (v : pqxdh.VerifiedInitKex) :
    ∃ r : pqxdh.RegistrationId,
      pqxdh.registration_id v = ok r ∧
        absBytes r.bytes =
          Pqxdh.ValidInit.rid ⟨absBytes v.beacon_identity_public_key,
            absBytes v.beacon_prekey_public_key, absBytes v.beacon_one_time_public_key,
            absBytes v.beacon_pq_public_key⟩ := by
  have hlen : (Pqxdh.ValidInit.rid ⟨absBytes v.beacon_identity_public_key,
      absBytes v.beacon_prekey_public_key, absBytes v.beacon_one_time_public_key,
      absBytes v.beacon_pq_public_key⟩).length = (64#usize).val := by
    simp [Pqxdh.ValidInit.rid]
  have hcall : ∀ i, i < (64#usize).val →
      pqxdh.VerifiedInitKex.registration_id.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
          v ⟨BitVec.ofNat _ i⟩
        = ok ((if i < 32 then v.beacon_identity_public_key.val[i]!
                else v.beacon_one_time_public_key.val[i - 32]!), v) := by
    intro i hi
    rw [usize_val_64] at hi
    have hval : (⟨BitVec.ofNat _ i⟩ : Std.Usize).val = i := usize_mk_val i (by omega)
    have hlt : ((⟨BitVec.ofNat _ i⟩ : Std.Usize) < pqxdh.SIGN_PUBLIC_KEY_SIZE) ↔ i < 32 := by
      rw [sign_public_key_size_eq, Std.UScalar.lt_equiv, hval, usize_val_32]
    unfold
      pqxdh.VerifiedInitKex.registration_id.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
    by_cases h : i < 32
    · rw [if_pos (hlt.mpr h), if_pos h,
        index_usize_eq v.beacon_identity_public_key _ (by rw [hval, usize_val_32]; omega), hval]
      rfl
    · rw [if_neg (fun hc => absurd (hlt.mp hc) h), if_neg h, sign_public_key_size_eq]
      have hsub : (32#usize).val ≤ (⟨BitVec.ofNat _ i⟩ : Std.Usize).val := by
        rw [usize_val_32, hval]; omega
      rw [usize_sub_eq _ _ hsub]
      have h1 : (⟨BitVec.ofNat _ ((⟨BitVec.ofNat _ i⟩ : Std.Usize).val - (32#usize).val)⟩ :
          Std.Usize).val = i - 32 := by
        rw [hval, usize_val_32]
        exact usize_mk_val (i - 32) (by omega)
      simp only [bind_tc_ok]
      rw [index_usize_eq v.beacon_one_time_public_key _ (by rw [h1, usize_val_32]; omega), h1]
      rfl
  have hbyte : ∀ i, i < (64#usize).val →
      absByte (if i < 32 then v.beacon_identity_public_key.val[i]!
                else v.beacon_one_time_public_key.val[i - 32]!)
        = (Pqxdh.ValidInit.rid ⟨absBytes v.beacon_identity_public_key,
            absBytes v.beacon_prekey_public_key, absBytes v.beacon_one_time_public_key,
            absBytes v.beacon_pq_public_key⟩)[i]! := by
    intro i hi
    rw [usize_val_64] at hi
    rw [Pqxdh.ValidInit.rid, getElem!_append2 _ _ 32 (by simp)]
    by_cases h : i < 32
    · rw [if_pos h, if_pos h]
      exact (absBytes_getElem! _ i (by rw [usize_val_32]; omega)).symm
    · rw [if_neg h, if_neg h]
      exact (absBytes_getElem! _ (i - 32) (by rw [usize_val_32]; omega)).symm
  obtain ⟨a, ha, habs⟩ :=
    from_fn_absBytes (F := pqxdh.VerifiedInitKex.registration_id.closure) 64#usize
      pqxdh.VerifiedInitKex.registration_id.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
      v _ _ hlen hcall hbyte
  refine ⟨⟨a⟩, ?_, habs⟩
  unfold pqxdh.registration_id pqxdh.VerifiedInitKex.registration_id
  rw [ha]
  rfl


/-! ## The associated data -/

@[simp] theorem absBytes_PQXDH_INFO : absBytes pqxdh.PQXDH_INFO = Pqxdh.INFO_PQ := by
  simp [absBytes, pqxdh.PQXDH_INFO, Pqxdh.INFO_PQ, absByte, Std.Array.make]

@[simp] theorem absBytes_SYM_RATCHET_INFO :
    absBytes pqxdh.SYM_RATCHET_INFO = Pqxdh.INFO_R := by
  simp [absBytes, pqxdh.SYM_RATCHET_INFO, ratchet.SYM_RATCHET_INFO, Pqxdh.INFO_R, absByte,
    Std.Array.make]

/-- The generated associated-data closure, with its captured pair destructured. -/
theorem build_associated_data_call_mut (a a1 : Std.Array Std.U8 33#usize) (t : Std.Usize) :
    pqxdh.build_associated_data.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
        ((a, a1) : pqxdh.build_associated_data.closure) t
      = (if t < 33#usize then
            Std.Array.index_usize a t >>= fun i =>
              ok (i, ((a, a1) : pqxdh.build_associated_data.closure))
          else if t < 66#usize then
            t - 33#usize >>= fun i => Std.Array.index_usize a1 i >>= fun i1 =>
              ok (i1, ((a, a1) : pqxdh.build_associated_data.closure))
          else if t < 112#usize then
            t - 66#usize >>= fun i => Std.Array.index_usize pqxdh.PQXDH_INFO i >>= fun i1 =>
              ok (i1, ((a, a1) : pqxdh.build_associated_data.closure))
          else
            t - 112#usize >>= fun i =>
              Std.Array.index_usize pqxdh.SYM_RATCHET_INFO i >>= fun i1 =>
                ok (i1, ((a, a1) : pqxdh.build_associated_data.closure))) := rfl

@[simp] theorem usize_val_46 : (46#usize).val = 46 := by scalar_tac
@[simp] theorem usize_val_41 : (41#usize).val = 41 := by scalar_tac
@[simp] theorem usize_val_66 : (66#usize).val = 66 := by scalar_tac
@[simp] theorem usize_val_112 : (112#usize).val = 112 := by scalar_tac

/-- The generated associated data is the ideal `AD` of spec §9. -/
theorem build_associated_data_abs (ikS ikB : Std.Array Std.U8 32#usize) :
    ∃ a : Std.Array Std.U8 153#usize,
      pqxdh.build_associated_data ikS ikB = ok a ∧
        absBytes a = Pqxdh.assocData (absBytes ikS) (absBytes ikB) := by
  obtain ⟨es, hes, hesabs⟩ := tag_sign_key_abs ikS
  obtain ⟨eb, heb, hebabs⟩ := tag_sign_key_abs ikB
  have hlen : (Pqxdh.assocData (absBytes ikS) (absBytes ikB)).length = (153#usize).val := by
    rw [usize_val_153]
    exact Pqxdh.assocData_length (by simp) (by simp)
  have hcall : ∀ i, i < (153#usize).val →
      pqxdh.build_associated_data.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
          ((es, eb) : pqxdh.build_associated_data.closure) ⟨BitVec.ofNat _ i⟩
        = ok ((if i < 33 then es.val[i]!
                else if i < 66 then eb.val[i - 33]!
                else if i < 112 then pqxdh.PQXDH_INFO.val[i - 66]!
                else pqxdh.SYM_RATCHET_INFO.val[i - 112]!),
              ((es, eb) : pqxdh.build_associated_data.closure)) := by
    intro i hi
    rw [usize_val_153] at hi
    have hval : (⟨BitVec.ofNat _ i⟩ : Std.Usize).val = i := usize_mk_val i (by omega)
    have hlt : ∀ k : Std.Usize, ((⟨BitVec.ofNat _ i⟩ : Std.Usize) < k) ↔ i < k.val := by
      intro k; rw [Std.UScalar.lt_equiv, hval]
    refine Eq.trans (build_associated_data_call_mut es eb _) ?_
    by_cases h33 : i < 33
    · rw [if_pos ((hlt _).mpr (by rw [usize_val_33]; omega)), if_pos h33,
        index_usize_eq es _ (by rw [hval, usize_val_33]; omega), hval]
      rfl
    · rw [if_neg (fun hc => h33 (by simpa [usize_val_33] using (hlt 33#usize).mp hc)),
        if_neg h33]
      have hsub33 : (33#usize).val ≤ (⟨BitVec.ofNat _ i⟩ : Std.Usize).val := by
        rw [usize_val_33, hval]; omega
      by_cases h66 : i < 66
      · rw [if_pos ((hlt _).mpr (by rw [usize_val_66]; omega)), if_pos h66,
          usize_sub_eq _ _ hsub33]
        have h1 : (⟨BitVec.ofNat _ ((⟨BitVec.ofNat _ i⟩ : Std.Usize).val - (33#usize).val)⟩ :
            Std.Usize).val = i - 33 := by
          rw [hval, usize_val_33]; exact usize_mk_val (i - 33) (by omega)
        simp only [bind_tc_ok]
        rw [index_usize_eq eb _ (by rw [h1, usize_val_33]; omega), h1]
        rfl
      · rw [if_neg (fun hc => h66 (by simpa [usize_val_66] using (hlt 66#usize).mp hc)),
          if_neg h66]
        have hsub66 : (66#usize).val ≤ (⟨BitVec.ofNat _ i⟩ : Std.Usize).val := by
          rw [usize_val_66, hval]; omega
        by_cases h112 : i < 112
        · rw [if_pos ((hlt _).mpr (by rw [usize_val_112]; omega)), if_pos h112,
            usize_sub_eq _ _ hsub66]
          have h1 : (⟨BitVec.ofNat _ ((⟨BitVec.ofNat _ i⟩ : Std.Usize).val - (66#usize).val)⟩ :
              Std.Usize).val = i - 66 := by
            rw [hval, usize_val_66]; exact usize_mk_val (i - 66) (by omega)
          simp only [bind_tc_ok]
          rw [index_usize_eq pqxdh.PQXDH_INFO _ (by rw [h1, usize_val_46]; omega), h1]
          rfl
        · rw [if_neg (fun hc => h112 (by simpa [usize_val_112] using (hlt 112#usize).mp hc)),
            if_neg h112]
          have hsub112 : (112#usize).val ≤ (⟨BitVec.ofNat _ i⟩ : Std.Usize).val := by
            rw [usize_val_112, hval]; omega
          rw [usize_sub_eq _ _ hsub112]
          have h1 : (⟨BitVec.ofNat _ ((⟨BitVec.ofNat _ i⟩ : Std.Usize).val - (112#usize).val)⟩ :
              Std.Usize).val = i - 112 := by
            rw [hval, usize_val_112]; exact usize_mk_val (i - 112) (by omega)
          simp only [bind_tc_ok]
          rw [index_usize_eq pqxdh.SYM_RATCHET_INFO _ (by rw [h1, usize_val_41]; omega), h1]
          rfl
  have hbyte : ∀ i, i < (153#usize).val →
      absByte (if i < 33 then es.val[i]!
                else if i < 66 then eb.val[i - 33]!
                else if i < 112 then pqxdh.PQXDH_INFO.val[i - 66]!
                else pqxdh.SYM_RATCHET_INFO.val[i - 112]!)
        = (Pqxdh.assocData (absBytes ikS) (absBytes ikB))[i]! := by
    intro i hi
    rw [usize_val_153] at hi
    rw [Pqxdh.assocData, getElem!_append2 _ _ 112 (by simp [Pqxdh.tagSig, Pqxdh.INFO_PQ]),
      getElem!_append2 _ _ 66 (by simp [Pqxdh.tagSig]),
      getElem!_append2 _ _ 33 (by simp [Pqxdh.tagSig])]
    by_cases h33 : i < 33
    · simp only [if_pos h33, if_pos (show i < 66 by omega), if_pos (show i < 112 by omega)]
      rw [← hesabs]
      exact (absBytes_getElem! es i (by rw [usize_val_33]; omega)).symm
    · by_cases h66 : i < 66
      · simp only [if_neg h33, if_pos h66, if_pos (show i < 112 by omega)]
        rw [← hebabs]
        exact (absBytes_getElem! eb (i - 33) (by rw [usize_val_33]; omega)).symm
      · by_cases h112 : i < 112
        · simp only [if_neg h33, if_neg h66, if_pos h112]
          rw [← absBytes_PQXDH_INFO]
          exact (absBytes_getElem! pqxdh.PQXDH_INFO (i - 66) (by rw [usize_val_46]; omega)).symm
        · simp only [if_neg h33, if_neg h66, if_neg h112]
          rw [← absBytes_SYM_RATCHET_INFO]
          exact (absBytes_getElem! pqxdh.SYM_RATCHET_INFO (i - 112)
            (by rw [usize_val_41]; omega)).symm
  obtain ⟨a, ha, habs⟩ :=
    from_fn_absBytes (F := pqxdh.build_associated_data.closure) 153#usize
      pqxdh.build_associated_data.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
      ((es, eb) : pqxdh.build_associated_data.closure) _ _ hlen hcall hbyte
  refine ⟨a, ?_, habs⟩
  unfold pqxdh.build_associated_data
  rw [hes]
  simp only [bind_tc_ok]
  rw [heb]
  simp only [bind_tc_ok]
  exact ha


/-! ## The PQXDH transcript -/

@[simp] theorem usize_val_3 : (3#usize).val = 3 := by scalar_tac
@[simp] theorem usize_val_4 : (4#usize).val = 4 := by scalar_tac
@[simp] theorem usize_val_96 : (96#usize).val = 96 := by scalar_tac
@[simp] theorem usize_val_128 : (128#usize).val = 128 := by scalar_tac
@[simp] theorem usize_val_160 : (160#usize).val = 160 := by scalar_tac

theorem usize_eq_of_val {x y : Std.Usize} (h : x.val = y.val) : x = y := by
  cases x; cases y
  simpa [Std.UScalar.val, BitVec.toNat_inj] using h

/-- Checked Rust multiplication of two `usize` constants. -/
theorem usize_mul_val (x y : Std.Usize) (h : x.val * y.val < 2 ^ System.Platform.numBits) :
    ∃ z : Std.Usize, x * y = ok z ∧ z.val = x.val * y.val := by
  have hb : Std.UScalar.inBounds .Usize (x.val * y.val) := h
  have hspec := Std.UScalar.tryMk_eq .Usize (x.val * y.val)
  show ∃ z, Std.UScalar.mul x y = ok z ∧ _
  unfold Std.UScalar.mul
  cases hc : Std.UScalar.tryMk (.Usize) (x.val * y.val) with
  | ok z => rw [hc] at hspec; exact ⟨z, rfl, hspec.1⟩
  | fail e => rw [hc] at hspec; exact absurd hb hspec
  | div => rw [hc] at hspec; exact absurd hspec (by simp)

theorem usize_mul_eq (x y z : Std.Usize) (h : x.val * y.val = z.val) : x * y = ok z := by
  obtain ⟨w, hw, hwv⟩ := usize_mul_val x y (by rw [h]; exact z.bv.isLt)
  rw [hw, usize_eq_of_val (show w.val = z.val by rw [hwv, h])]

theorem usize_add_eq (x y z : Std.Usize) (h : x.val + y.val = z.val) : x + y = ok z := by
  obtain ⟨w, hw, hwv⟩ := usize_add_val x y (by rw [h]; exact z.bv.isLt)
  rw [hw, usize_eq_of_val (show w.val = z.val by rw [hwv, h])]

@[simp] theorem absByte_255 : absByte 255#u8 = 0xFF := by simp [absByte]

theorem padFF32_getElem! (i : ℕ) (h : i < 32) : Pqxdh.padFF32[i]! = 0xFF := by
  rw [Pqxdh.padFF32, getElem!_pos (List.replicate 32 (0xFF : UInt8)) i (by simpa using h),
    List.getElem_replicate]

/-- The generated PQXDH transcript builder rejects an all-zero contribution exactly as
the ideal model does, and otherwise computes the ideal transcript `IKM_PQ`. -/
theorem build_root_key_input_abs (secrets : pqxdh.PqxdhSharedSecrets) :
    (Pqxdh.dhNonZero (absBytes secrets.dh1, absBytes secrets.dh2, absBytes secrets.dh3,
        absBytes secrets.dh4) →
      ∃ v : pqxdh.RootKeyInput,
        pqxdh.build_root_key_input secrets = ok (core.result.Result.Ok v) ∧
          absBytes v.bytes = Pqxdh.pqxdhIKM (absBytes secrets.dh1) (absBytes secrets.dh2)
            (absBytes secrets.dh3) (absBytes secrets.dh4)
            (absBytes secrets.kem_shared_secret)) ∧
    (¬ Pqxdh.dhNonZero (absBytes secrets.dh1, absBytes secrets.dh2, absBytes secrets.dh3,
        absBytes secrets.dh4) →
      pqxdh.build_root_key_input secrets =
        ok (core.result.Result.Err pqxdh.RegistrationError.InvalidDhOutput)) := by
  have hunf : pqxdh.build_root_key_input secrets =
      (if absBytes secrets.dh1 = Pqxdh.zero32 then
        ok (core.result.Result.Err pqxdh.RegistrationError.InvalidDhOutput)
       else if absBytes secrets.dh2 = Pqxdh.zero32 then
        ok (core.result.Result.Err pqxdh.RegistrationError.InvalidDhOutput)
       else if absBytes secrets.dh3 = Pqxdh.zero32 then
        ok (core.result.Result.Err pqxdh.RegistrationError.InvalidDhOutput)
       else if absBytes secrets.dh4 = Pqxdh.zero32 then
        ok (core.result.Result.Err pqxdh.RegistrationError.InvalidDhOutput)
       else
        (core.array.from_fn 192#usize
            pqxdh.build_root_key_input.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8 secrets
          >>= fun bytes => ok (core.result.Result.Ok ⟨bytes⟩))) := by
    unfold pqxdh.build_root_key_input
    rw [is_all_zero_abs, is_all_zero_abs, is_all_zero_abs, is_all_zero_abs]
    simp only [bind_tc_ok]
    by_cases h1 : absBytes secrets.dh1 = Pqxdh.zero32
    · simp only [h1, decide_true, if_true]
    · simp only [h1, decide_false, Bool.false_eq_true, ite_false]
      by_cases h2 : absBytes secrets.dh2 = Pqxdh.zero32
      · simp only [h2, decide_true, if_true]
      · simp only [h2, decide_false, Bool.false_eq_true, ite_false]
        by_cases h3 : absBytes secrets.dh3 = Pqxdh.zero32
        · simp only [h3, decide_true, if_true]
        · simp only [h3, decide_false, Bool.false_eq_true, ite_false]
          by_cases h4 : absBytes secrets.dh4 = Pqxdh.zero32
          · simp only [h4, decide_true, if_true]
          · simp only [h4, decide_false, Bool.false_eq_true, ite_false]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hlen : (Pqxdh.pqxdhIKM (absBytes secrets.dh1) (absBytes secrets.dh2)
        (absBytes secrets.dh3) (absBytes secrets.dh4)
        (absBytes secrets.kem_shared_secret)).length = (192#usize).val := by
      rw [usize_val_192]
      exact Pqxdh.pqxdhIKM_length (by simp) (by simp) (by simp) (by simp) (by simp)
    have hcall : ∀ i, i < (192#usize).val →
        pqxdh.build_root_key_input.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
            secrets ⟨BitVec.ofNat _ i⟩
          = ok ((if i < 32 then 255#u8
                  else if i < 64 then secrets.dh1.val[i - 32]!
                  else if i < 96 then secrets.dh2.val[i - 64]!
                  else if i < 128 then secrets.dh3.val[i - 96]!
                  else if i < 160 then secrets.dh4.val[i - 128]!
                  else secrets.kem_shared_secret.val[i - 160]!), secrets) := by
      intro i hi
      rw [usize_val_192] at hi
      have hval : (⟨BitVec.ofNat _ i⟩ : Std.Usize).val = i := usize_mk_val i (by omega)
      have hlt : ∀ k : Std.Usize, ((⟨BitVec.ofNat _ i⟩ : Std.Usize) < k) ↔ i < k.val := by
        intro k; rw [Std.UScalar.lt_equiv, hval]
      have a1 : (32#usize : Std.Usize) + 32#usize = ok 64#usize := usize_add_eq _ _ _ (by simp)
      have a2 : (2#usize : Std.Usize) * 32#usize = ok 64#usize := usize_mul_eq _ _ _ (by simp)
      have a3 : (32#usize : Std.Usize) + 64#usize = ok 96#usize := usize_add_eq _ _ _ (by simp)
      have a4 : (3#usize : Std.Usize) * 32#usize = ok 96#usize := usize_mul_eq _ _ _ (by simp)
      have a5 : (32#usize : Std.Usize) + 96#usize = ok 128#usize := usize_add_eq _ _ _ (by simp)
      have a6 : (4#usize : Std.Usize) * 32#usize = ok 128#usize := usize_mul_eq _ _ _ (by simp)
      have a7 : (32#usize : Std.Usize) + 128#usize = ok 160#usize := usize_add_eq _ _ _ (by simp)
      have hsub : ∀ (k : Std.Usize) (m : ℕ), k.val = m → m ≤ i →
          ((⟨BitVec.ofNat _ i⟩ : Std.Usize) - k) = ok ⟨BitVec.ofNat _ (i - m)⟩ := by
        intro k m hk hm
        rw [usize_sub_eq _ _ (by rw [hk, hval]; omega), hval, hk]
      have hsubv : ∀ m : ℕ, m ≤ i → (⟨BitVec.ofNat _ (i - m)⟩ : Std.Usize).val = i - m := by
        intro m _; exact usize_mk_val (i - m) (by omega)
      unfold pqxdh.build_root_key_input.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
      rw [pqxdh_padding_size_eq, dh_secret_size_eq]
      by_cases h32 : i < 32
      · rw [if_pos ((hlt _).mpr (by rw [usize_val_32]; omega))]
        simp only [if_pos h32]
      · rw [if_neg (fun hc => h32 (by simpa [usize_val_32] using (hlt 32#usize).mp hc)), a1]
        simp only [bind_tc_ok, if_neg h32]
        by_cases h64 : i < 64
        · rw [if_pos ((hlt _).mpr (by rw [usize_val_64]; omega)),
            hsub 32#usize 32 (by simp) (by omega)]
          simp only [bind_tc_ok, if_pos h64]
          rw [index_usize_eq secrets.dh1 _ (by rw [hsubv 32 (by omega), usize_val_32]; omega),
            hsubv 32 (by omega)]
          rfl
        · rw [if_neg (fun hc => h64 (by simpa [usize_val_64] using (hlt 64#usize).mp hc)),
            a2]
          simp only [bind_tc_ok, if_neg h64]
          rw [a3]
          simp only [bind_tc_ok]
          by_cases h96 : i < 96
          · rw [if_pos ((hlt _).mpr (by rw [usize_val_96]; omega)),
              hsub 32#usize 32 (by simp) (by omega)]
            simp only [bind_tc_ok]
            rw [show ((⟨BitVec.ofNat _ (i - 32)⟩ : Std.Usize) - 32#usize)
                = ok ⟨BitVec.ofNat _ (i - 64)⟩ from by
              rw [usize_sub_eq _ _ (by rw [hsubv 32 (by omega), usize_val_32]; omega),
                hsubv 32 (by omega), usize_val_32]
              congr 2]
            simp only [bind_tc_ok, if_pos h96]
            rw [index_usize_eq secrets.dh2 _ (by rw [hsubv 64 (by omega), usize_val_32]; omega),
              hsubv 64 (by omega)]
            rfl
          · rw [if_neg (fun hc => h96 (by simpa [usize_val_96] using (hlt 96#usize).mp hc)),
              a4]
            simp only [bind_tc_ok]
            rw [a5]
            simp only [bind_tc_ok, if_neg h96]
            by_cases h128 : i < 128
            · rw [if_pos ((hlt _).mpr (by rw [usize_val_128]; omega)),
                hsub 32#usize 32 (by simp) (by omega)]
              simp only [bind_tc_ok]
              rw [show ((⟨BitVec.ofNat _ (i - 32)⟩ : Std.Usize) - 64#usize)
                  = ok ⟨BitVec.ofNat _ (i - 96)⟩ from by
                rw [usize_sub_eq _ _ (by rw [hsubv 32 (by omega), usize_val_64]; omega),
                  hsubv 32 (by omega), usize_val_64]
                congr 2]
              simp only [bind_tc_ok, if_pos h128]
              rw [index_usize_eq secrets.dh3 _ (by rw [hsubv 96 (by omega), usize_val_32]; omega),
                hsubv 96 (by omega)]
              rfl
            · rw [if_neg (fun hc => h128 (by simpa [usize_val_128] using (hlt 128#usize).mp hc)),
                a6]
              simp only [bind_tc_ok]
              rw [a7]
              simp only [bind_tc_ok, if_neg h128]
              by_cases h160 : i < 160
              · rw [if_pos ((hlt _).mpr (by rw [usize_val_160]; omega)),
                  hsub 32#usize 32 (by simp) (by omega)]
                simp only [bind_tc_ok]
                rw [show ((⟨BitVec.ofNat _ (i - 32)⟩ : Std.Usize) - 96#usize)
                    = ok ⟨BitVec.ofNat _ (i - 128)⟩ from by
                  rw [usize_sub_eq _ _ (by rw [hsubv 32 (by omega), usize_val_96]; omega),
                    hsubv 32 (by omega), usize_val_96]
                  congr 2]
                simp only [bind_tc_ok, if_pos h160]
                rw [index_usize_eq secrets.dh4 _
                    (by rw [hsubv 128 (by omega), usize_val_32]; omega),
                  hsubv 128 (by omega)]
                rfl
              · rw [if_neg (fun hc => h160 (by simpa [usize_val_160] using (hlt 160#usize).mp hc)),
                  hsub 32#usize 32 (by simp) (by omega)]
                simp only [bind_tc_ok]
                rw [show ((⟨BitVec.ofNat _ (i - 32)⟩ : Std.Usize) - 128#usize)
                    = ok ⟨BitVec.ofNat _ (i - 160)⟩ from by
                  rw [usize_sub_eq _ _ (by rw [hsubv 32 (by omega), usize_val_128]; omega),
                    hsubv 32 (by omega), usize_val_128]
                  congr 2]
                simp only [bind_tc_ok, if_neg h160]
                rw [index_usize_eq secrets.kem_shared_secret _
                    (by rw [hsubv 160 (by omega), usize_val_32]; omega),
                  hsubv 160 (by omega)]
                rfl
    have hbyte : ∀ i, i < (192#usize).val →
        absByte (if i < 32 then 255#u8
                  else if i < 64 then secrets.dh1.val[i - 32]!
                  else if i < 96 then secrets.dh2.val[i - 64]!
                  else if i < 128 then secrets.dh3.val[i - 96]!
                  else if i < 160 then secrets.dh4.val[i - 128]!
                  else secrets.kem_shared_secret.val[i - 160]!)
          = (Pqxdh.pqxdhIKM (absBytes secrets.dh1) (absBytes secrets.dh2)
              (absBytes secrets.dh3) (absBytes secrets.dh4)
              (absBytes secrets.kem_shared_secret))[i]! := by
      intro i hi
      rw [usize_val_192] at hi
      rw [Pqxdh.pqxdhIKM, getElem!_append2 _ _ 160 (by simp [Pqxdh.padFF32]),
        getElem!_append2 _ _ 128 (by simp [Pqxdh.padFF32]),
        getElem!_append2 _ _ 96 (by simp [Pqxdh.padFF32]),
        getElem!_append2 _ _ 64 (by simp [Pqxdh.padFF32]),
        getElem!_append2 _ _ 32 (by simp [Pqxdh.padFF32])]
      by_cases h32 : i < 32
      · simp only [if_pos h32, if_pos (show i < 64 by omega), if_pos (show i < 96 by omega),
          if_pos (show i < 128 by omega), if_pos (show i < 160 by omega)]
        rw [padFF32_getElem! i h32, absByte_255]
      · by_cases h64 : i < 64
        · simp only [if_neg h32, if_pos h64, if_pos (show i < 96 by omega),
            if_pos (show i < 128 by omega), if_pos (show i < 160 by omega)]
          exact (absBytes_getElem! secrets.dh1 (i - 32) (by rw [usize_val_32]; omega)).symm
        · by_cases h96 : i < 96
          · simp only [if_neg h32, if_neg h64, if_pos h96, if_pos (show i < 128 by omega),
              if_pos (show i < 160 by omega)]
            exact (absBytes_getElem! secrets.dh2 (i - 64) (by rw [usize_val_32]; omega)).symm
          · by_cases h128 : i < 128
            · simp only [if_neg h32, if_neg h64, if_neg h96, if_pos h128,
                if_pos (show i < 160 by omega)]
              exact (absBytes_getElem! secrets.dh3 (i - 96) (by rw [usize_val_32]; omega)).symm
            · by_cases h160 : i < 160
              · simp only [if_neg h32, if_neg h64, if_neg h96, if_neg h128, if_pos h160]
                exact (absBytes_getElem! secrets.dh4 (i - 128) (by rw [usize_val_32]; omega)).symm
              · simp only [if_neg h32, if_neg h64, if_neg h96, if_neg h128, if_neg h160]
                exact (absBytes_getElem! secrets.kem_shared_secret (i - 160)
                  (by rw [usize_val_32]; omega)).symm
    obtain ⟨a, ha, habs⟩ :=
      from_fn_absBytes (F := pqxdh.build_root_key_input.closure) 192#usize
        pqxdh.build_root_key_input.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
        secrets _ _ hlen hcall hbyte
    refine ⟨⟨a⟩, ?_, habs⟩
    rw [hunf, if_neg h1, if_neg h2, if_neg h3, if_neg h4, ha]
    rfl
  · intro h
    rw [Pqxdh.dhNonZero] at h
    push Not at h
    rw [hunf]
    by_cases h1 : absBytes secrets.dh1 = Pqxdh.zero32
    · rw [if_pos h1]
    · rw [if_neg h1]
      by_cases h2 : absBytes secrets.dh2 = Pqxdh.zero32
      · rw [if_pos h2]
      · rw [if_neg h2]
        by_cases h3 : absBytes secrets.dh3 = Pqxdh.zero32
        · rw [if_pos h3]
        · rw [if_neg h3]
          rw [if_pos (h h1 h2 h3)]

/-! ## The little-endian key-identifier binding (spec §12) -/

/-- A right shift of a `u64` by a nonnegative constant smaller than 64 never fails and
divides by the corresponding power of two. -/
theorem u64_shr_val (x : Std.U64) (k : Std.I32) (m : ℕ) (h0 : (0:ℤ) ≤ k.val)
    (hm : Std.IScalar.toNat k = m) (h1 : m < 64) :
    ∃ z : Std.U64, (x >>> k) = ok z ∧ z.val = x.val / 2 ^ m := by
  refine ⟨⟨x.bv.ushiftRight m⟩, ?_, ?_⟩
  · show Std.UScalar.shiftRight_IScalar x k = _
    unfold Std.UScalar.shiftRight_IScalar Std.UScalar.shiftRight
    rw [if_pos h0, hm, if_pos (show m < Std.UScalarTy.U64.numBits from h1)]
  · show (BitVec.ushiftRight x.bv m).toNat = _
    rw [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rfl

/-- **Refinement of the key-identifier binding.** The eight bytes the generated code
derives from a `u64` key identifier by shifting and truncating are exactly the ideal
little-endian encoding `Pqxdh.LE64`. -/
theorem registration_key_id_binding_abs (key_id : Std.U64) :
    ∃ b, pqxdh.registration_key_id_binding key_id = ok b ∧
      absBytes b.bytes = Pqxdh.LE64 key_id.val := by
  unfold pqxdh.registration_key_id_binding
  obtain ⟨z1, e1, v1⟩ := u64_shr_val key_id 8#i32 8 (by decide) (by decide) (by decide)
  obtain ⟨z2, e2, v2⟩ := u64_shr_val key_id 16#i32 16 (by decide) (by decide) (by decide)
  obtain ⟨z3, e3, v3⟩ := u64_shr_val key_id 24#i32 24 (by decide) (by decide) (by decide)
  obtain ⟨z4, e4, v4⟩ := u64_shr_val key_id 32#i32 32 (by decide) (by decide) (by decide)
  obtain ⟨z5, e5, v5⟩ := u64_shr_val key_id 40#i32 40 (by decide) (by decide) (by decide)
  obtain ⟨z6, e6, v6⟩ := u64_shr_val key_id 48#i32 48 (by decide) (by decide) (by decide)
  obtain ⟨z7, e7, v7⟩ := u64_shr_val key_id 56#i32 56 (by decide) (by decide) (by decide)
  rw [e1, e2, e3, e4, e5, e6, e7]
  simp only [bind_tc_ok]
  refine ⟨_, rfl, ?_⟩
  simp [absBytes, Pqxdh.LE64, Std.Array.make, absByte, Std.UScalar.cast_val_eq,
    v1, v2, v3, v4, v5, v6, v7, List.range_succ]

end PqxdhRefinement

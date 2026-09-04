import BeaconcryptCore.Refinement.PqxdhSurface

/-! Raw extracted commitment encodings, input injectivity, and constructive collision witnesses. No collision-resistance or AEAD correctness assumption is used. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
open BeaconcryptCore.Refinement.PqxdhSurface

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BeaconcryptCore.Refinement.CommitmentSurface

/-- The six fixed-width inputs accepted by the production transcript builder. -/
structure Fields where
  key : Std.Array Std.U8 32#usize
  nonce : Std.Array Std.U8 12#usize
  associatedData : Std.Array Std.U8 153#usize
  tag : Std.Array Std.U8 16#usize
  sequence : Std.U64
  senderId : Std.U64

noncomputable def productionTranscript (fields : Fields) : commitment.CommitmentTranscript :=
  (build_commitment_transcript_abs fields.key fields.nonce fields.associatedData fields.tag
    fields.sequence fields.senderId).choose

noncomputable def productionInput (fields : Fields) : Std.Array Std.U8 229#usize :=
  (productionTranscript fields).bytes

/-- This pure view is precisely the extracted builder's result, on all concrete input fields. -/
theorem productionInput_spec (fields : Fields) :
    commitment.build_commitment_transcript fields.key fields.nonce fields.associatedData fields.tag
      fields.sequence fields.senderId = ok { bytes := productionInput fields } :=
  (build_commitment_transcript_abs fields.key fields.nonce fields.associatedData fields.tag
    fields.sequence fields.senderId).choose_spec.1

theorem productionInput_abs (fields : Fields) :
    absBytes (productionInput fields) = Pqxdh.ctxPreimage (absBytes fields.key, absBytes fields.nonce)
      ⟨absBytes fields.associatedData, fields.sequence.val, fields.senderId.val⟩ (absBytes fields.tag) :=
  (build_commitment_transcript_abs fields.key fields.nonce fields.associatedData fields.tag
    fields.sequence fields.senderId).choose_spec.2

theorem fields_well_formed (fields : Fields) :
    Pqxdh.RecordWf (absBytes fields.key, absBytes fields.nonce)
      ⟨absBytes fields.associatedData, fields.sequence.val, fields.senderId.val⟩ :=
  ⟨by simp, by simp, by simp, fields.sequence.bv.isLt, fields.senderId.bv.isLt⟩

theorem fields_ext (left right : Fields)
    (hk : left.key = right.key) (hn : left.nonce = right.nonce)
    (ha : left.associatedData = right.associatedData) (ht : left.tag = right.tag)
    (hs : left.sequence = right.sequence) (hi : left.senderId = right.senderId) : left = right := by
  cases left; cases right; simp_all

/-- Equality of actual extracted transcript bytes determines all six concrete fields. -/
theorem production_commitment_input_is_injective : Function.Injective productionInput := by
  intro left right heq
  have h := Pqxdh.ctxPreimage_inj (fields_well_formed left) (fields_well_formed right)
    (by simp) (by simp) ((productionInput_abs left).symm.trans
      ((congrArg absBytes heq).trans (productionInput_abs right)))
  exact fields_ext left right
    (bytes_eq_of_abs_eq (congrArg Prod.fst h.1))
    (bytes_eq_of_abs_eq (congrArg Prod.snd h.1))
    (bytes_eq_of_abs_eq (congrArg Pqxdh.RecordAD.bytes h.2.1))
    (bytes_eq_of_abs_eq h.2.2)
    (Std.UScalar.eq_of_val_eq (congrArg Pqxdh.RecordAD.seq h.2.1))
    (Std.UScalar.eq_of_val_eq (congrArg Pqxdh.RecordAD.sid h.2.1))

def OpeningAccepted {Ciphertext Plaintext : Type}
    (hash : Std.Array Std.U8 229#usize → Std.Array Std.U8 64#usize)
    (aeadOpen : Std.Array Std.U8 32#usize → Std.Array Std.U8 12#usize →
      Std.Array Std.U8 153#usize → Ciphertext → Std.Array Std.U8 16#usize → core.option.Option Plaintext)
    (ciphertext : Ciphertext) (digest : Std.Array Std.U8 64#usize) (fields : Fields) (plaintext : Plaintext) : Prop :=
  hash (productionInput fields) = digest ∧
    aeadOpen fields.key fields.nonce fields.associatedData ciphertext fields.tag = .Some plaintext

def ExplanationsDistinct {Plaintext : Type} (left right : Fields) (leftPlaintext rightPlaintext : Plaintext) : Prop :=
  left.key ≠ right.key ∨ left.nonce ≠ right.nonce ∨ left.associatedData ≠ right.associatedData ∨
    left.sequence ≠ right.sequence ∨ left.senderId ≠ right.senderId ∨ leftPlaintext ≠ rightPlaintext

structure HashCollisionWitness where
  leftInput : Std.Array Std.U8 229#usize
  rightInput : Std.Array Std.U8 229#usize

def ValidHashCollisionWitness
    (hash : Std.Array Std.U8 229#usize → Std.Array Std.U8 64#usize) (witness : HashCollisionWitness) : Prop :=
  witness.leftInput ≠ witness.rightInput ∧ hash witness.leftInput = hash witness.rightInput

/-- Two distinct accepted explanations yield the actual pair of different production inputs with one hash output. AEAD determinism alone handles differing plaintexts. -/
theorem ctx_distinct_openings_imply_hash_collision {Ciphertext Plaintext : Type}
    (hash : Std.Array Std.U8 229#usize → Std.Array Std.U8 64#usize)
    (aeadOpen : Std.Array Std.U8 32#usize → Std.Array Std.U8 12#usize →
      Std.Array Std.U8 153#usize → Ciphertext → Std.Array Std.U8 16#usize → core.option.Option Plaintext)
    (ciphertext : Ciphertext) (digest : Std.Array Std.U8 64#usize)
    (left right : Fields) (leftPlaintext rightPlaintext : Plaintext)
    (hleft : OpeningAccepted hash aeadOpen ciphertext digest left leftPlaintext)
    (hright : OpeningAccepted hash aeadOpen ciphertext digest right rightPlaintext)
    (hdistinct : ExplanationsDistinct left right leftPlaintext rightPlaintext) :
    ∃ witness : HashCollisionWitness,
      witness.leftInput = productionInput left ∧ witness.rightInput = productionInput right ∧
      ValidHashCollisionWitness hash witness := by
  refine ⟨⟨productionInput left, productionInput right⟩, rfl, rfl, ?_, hleft.1.trans hright.1.symm⟩
  intro heq
  have hfields := production_commitment_input_is_injective heq
  have hplaintext : leftPlaintext = rightPlaintext := by
    simpa using hleft.2.symm.trans
      ((congrArg (fun fields : Fields => aeadOpen fields.key fields.nonce fields.associatedData ciphertext fields.tag)
        hfields).trans hright.2)
  simp [ExplanationsDistinct, hfields, hplaintext] at hdistinct

/-- The mathematical little-endian decoder used in the F* proof, over the same concrete eight bytes. -/
def decode_u64_le (bytes : Std.Array Std.U8 8#usize) : Nat :=
  (absBytes bytes)[0]!.toNat + 256 * (absBytes bytes)[1]!.toNat +
    65536 * (absBytes bytes)[2]!.toNat + 16777216 * (absBytes bytes)[3]!.toNat +
    4294967296 * (absBytes bytes)[4]!.toNat + 1099511627776 * (absBytes bytes)[5]!.toNat +
    281474976710656 * (absBytes bytes)[6]!.toNat + 72057594037927936 * (absBytes bytes)[7]!.toNat

theorem decode_u64_le_of_abs (bytes : Std.Array Std.U8 8#usize) (value : Std.U64)
    (hbytes : absBytes bytes = Pqxdh.LE64 value.val) : decode_u64_le bytes = value.val := by
  simp [decode_u64_le, hbytes, Pqxdh.LE64, List.range_succ]
  have hlt : value.val < 2 ^ 64 := value.bv.isLt
  omega

theorem decode_encode_u64_le (value : Std.U64) :
    ∃ bytes, commitment.encode_u64_le value = ok bytes ∧ decode_u64_le bytes = value.val :=
  (commitment_encode_u64_le_abs value).elim fun bytes hbytes =>
    ⟨bytes, hbytes.1, decode_u64_le_of_abs bytes value hbytes.2⟩

/-- Equal extracted encoder executions imply equal integers over the entire u64 domain. -/
theorem encode_u64_le_is_injective (left right : Std.U64)
    (heq : commitment.encode_u64_le left = commitment.encode_u64_le right) : left = right :=
  (commitment_encode_u64_le_abs left).elim fun leftBytes hl =>
  (commitment_encode_u64_le_abs right).elim fun rightBytes hr =>
    let hbytes : leftBytes = rightBytes := by simpa using hl.1.symm.trans (heq.trans hr.1)
    Std.UScalar.eq_of_val_eq (Pqxdh.LE64_inj left.bv.isLt right.bv.isLt
      (hl.2.symm.trans ((congrArg absBytes hbytes).trans hr.2)))

end BeaconcryptCore.Refinement.CommitmentSurface

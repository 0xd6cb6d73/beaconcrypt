-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Model.Pqxdh.Primitives

/-!
Exact record-AD framing for registration version 3. The four remaining Init fields retain all attached Ed25519 signature bytes. Response application ciphertext and ML-DSA signature are intentionally absent: this transcript is needed before sealing. Hashing is an external operation; none of these statements assumes an injective hash or proves primitive security.
-/
set_option autoImplicit false
set_option warningAsError true
namespace Pqxdh.SessionTranscript

@[ext] structure InitFields where
  identityKey : Bytes
  preKey : Bytes
  oneTimeKey : Bytes
  pqKey : Bytes
  deriving DecidableEq

structure InitFields.WellFormed (init : InitFields) : Prop where
  identityWidth : init.identityKey.length = 33
  preWidth : init.preKey.length = 98
  oneTimeWidth : init.oneTimeKey.length = 98
  pqWidth : init.pqKey.length = 1249

@[ext] structure ResponseFields where
  identityKey : Bytes
  ephemeralKey : Bytes
  kemCipherText : Bytes
  keyId : UInt64
  deriving DecidableEq

structure ResponseFields.WellFormed (response : ResponseFields) : Prop where
  identityWidth : response.identityKey.length = 32
  ephemeralWidth : response.ephemeralKey.length = 32
  kemWidth : response.kemCipherText.length = 1088

/-- Retained context bytes, independent of all current HKDF request labels. -/
def context : Bytes :=
  [66, 101, 97, 99, 111, 110, 99, 114, 121, 112, 116, 80, 113, 120, 100, 104, 95, 67, 85, 82, 86, 69, 50, 53, 53, 49, 57, 95, 83, 72, 65, 45, 53, 49, 50, 95, 77, 76, 45, 75, 69, 77, 45, 55, 54, 56, 83, 121, 109, 82, 97, 116, 99, 104, 101, 116, 95, 72, 75, 68, 70, 95, 83, 72, 65, 45, 53, 49, 50, 95, 67, 72, 65, 67, 72, 65, 50, 48, 95, 80, 79, 76, 89, 49, 51, 48, 53]

/-- The owned request block retains complete signed buffers in wire field order. -/
def initBlock (init : InitFields) : Bytes :=
  init.identityKey ++ init.preKey ++ init.oneTimeKey ++ init.pqKey

/-- Exact fixed-position preimage. There are no additional lengths, domains, pins, or application fields. -/
def encode (init : InitFields) (response : ResponseFields) : Bytes :=
  initBlock init ++ response.identityKey ++ response.ephemeralKey ++
    response.kemCipherText ++ LE64 response.keyId.toNat

/-- The context is retained outside the external BLAKE2b-512 digest. -/
def associatedData (digest : Bytes) : Bytes := context ++ digest

theorem context_length : context.length = 87 := rfl

theorem initBlock_length (init : InitFields) (valid : init.WellFormed) :
    (initBlock init).length = 1478 := by
  simp only [initBlock, List.length_append, valid.identityWidth, valid.preWidth,
    valid.oneTimeWidth, valid.pqWidth]

theorem encode_length (init : InitFields) (response : ResponseFields)
    (validInit : init.WellFormed) (validResponse : response.WellFormed) :
    (encode init response).length = 2638 := by
  simp only [encode, List.length_append, initBlock_length init validInit,
    validResponse.identityWidth, validResponse.ephemeralWidth, validResponse.kemWidth,
    LE64_length]

theorem associatedData_length (digest : Bytes) (width : digest.length = 64) :
    (associatedData digest).length = 151 := by
  simp only [associatedData, List.length_append, context_length, width]

/-- Exact fixed-offset decomposition preserves signatures and tags without reopening keys. -/
theorem encode_fields (init : InitFields) (response : ResponseFields)
    (validInit : init.WellFormed) (validResponse : response.WellFormed) :
    (encode init response).take 33 = init.identityKey ∧
    ((encode init response).drop 33).take 98 = init.preKey ∧
    ((encode init response).drop 131).take 98 = init.oneTimeKey ∧
    ((encode init response).drop 229).take 1249 = init.pqKey ∧
    ((encode init response).drop 1478).take 32 = response.identityKey ∧
    ((encode init response).drop 1510).take 32 = response.ephemeralKey ∧
    ((encode init response).drop 1542).take 1088 = response.kemCipherText ∧
    (encode init response).drop 2630 = LE64 response.keyId.toNat := by
  simp [encode, initBlock, List.append_assoc, List.drop_append, List.drop_eq_nil_of_le,
    validInit.identityWidth, validInit.preWidth, validInit.oneTimeWidth,
    validInit.pqWidth, validResponse.identityWidth, validResponse.ephemeralWidth,
    validResponse.kemWidth]

/-- Fixed framing determines every original field before hashing. -/
theorem encode_inj {leftInit rightInit : InitFields} {leftResponse rightResponse : ResponseFields}
    (leftInitValid : leftInit.WellFormed) (rightInitValid : rightInit.WellFormed)
    (leftResponseValid : leftResponse.WellFormed) (rightResponseValid : rightResponse.WellFormed)
    (same : encode leftInit leftResponse = encode rightInit rightResponse) :
    leftInit = rightInit ∧ leftResponse = rightResponse := by
  have left := encode_fields leftInit leftResponse leftInitValid leftResponseValid
  rw [same] at left
  rcases encode_fields rightInit rightResponse rightInitValid rightResponseValid with
    ⟨identity, preKey, oneTime, pqKey, server, ephemeral, kem, keyId⟩
  simp only [identity, preKey, oneTime, pqKey, server, ephemeral, kem, keyId] at left
  exact ⟨(InitFields.ext left.1 left.2.1 left.2.2.1 left.2.2.2.1).symm,
    (ResponseFields.ext left.2.2.2.2.1 left.2.2.2.2.2.1 left.2.2.2.2.2.2.1
      (UInt64.toNat_inj.mp (LE64_inj rightResponse.keyId.toNat_lt
        leftResponse.keyId.toNat_lt left.2.2.2.2.2.2.2))).symm⟩

/-- The retained fixed prefix preserves exact digest equality. -/
theorem associatedData_inj (left right : Bytes)
    (same : associatedData left = associatedData right) : left = right := by
  simpa only [associatedData, List.append_right_inj] using same

end Pqxdh.SessionTranscript

/-- info: 'Pqxdh.SessionTranscript.context_length' does not depend on any axioms -/
#guard_msgs in
#print axioms Pqxdh.SessionTranscript.context_length

/-- info: 'Pqxdh.SessionTranscript.initBlock_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Pqxdh.SessionTranscript.initBlock_length

/-- info: 'Pqxdh.SessionTranscript.encode_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Pqxdh.SessionTranscript.encode_length

/-- info: 'Pqxdh.SessionTranscript.associatedData_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Pqxdh.SessionTranscript.associatedData_length

/-- info: 'Pqxdh.SessionTranscript.encode_fields' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pqxdh.SessionTranscript.encode_fields

/-- info: 'Pqxdh.SessionTranscript.encode_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pqxdh.SessionTranscript.encode_inj

/-- info: 'Pqxdh.SessionTranscript.associatedData_inj' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Pqxdh.SessionTranscript.associatedData_inj

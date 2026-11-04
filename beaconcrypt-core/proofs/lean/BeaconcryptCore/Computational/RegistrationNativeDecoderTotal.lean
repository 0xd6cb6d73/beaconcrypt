-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSourceWire
import BeaconcryptCore.Refinement.RegistrationPublicDecoderTotal
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
/-! Complete normality of the actual public decoders composed with the extracted packet constructors. The native optional facades retain precisely those ordinary replies on every hostile byte input. -/
namespace BeaconcryptCore.Computational.RegistrationNativeDecoderTotal
open BeaconcryptCore.Refinement

theorem init_total [RegistrationValidatorPrimitive.Operations] (input : Slice U8) :
    ∃ reply, RegistrationNativePacketReadback.decodeInit input = .ok reply := by
  obtain ⟨parsed, source, _⟩ := RegistrationPublicDecoderTotal.init_total input
  rw [RegistrationNativePacketReadback.decodeInit, source]
  cases parsed with
  | none => exact ⟨.None, rfl⟩
  | some value =>
    obtain ⟨reply, run, _⟩ := RegistrationInputs.init_packet_exact value.identity_key value.pre_key
      value.one_time_key value.pq_key value.mldsa_public_key value.signature
    exact ⟨reply, by simpa only [bind_tc_ok] using run⟩

theorem response_total [RegistrationValidatorPrimitive.Operations] (input : Slice U8) :
    ∃ reply, RegistrationNativePacketReadback.decodeResponse input = .ok reply := by
  obtain ⟨parsed, source, _⟩ := RegistrationPublicDecoderTotal.response_total input
  rw [RegistrationNativePacketReadback.decodeResponse, source]
  cases parsed with
  | none => exact ⟨.None, rfl⟩
  | some value =>
    obtain ⟨reply, run, _⟩ := RegistrationInputs.response_packet_exact value.identity_key value.ephemeral_key
      value.kem_cipher_text value.key_id value.app_cipher_text value.signature
    exact ⟨reply, by simpa only [bind_tc_ok] using run⟩

theorem init_oversize [RegistrationValidatorPrimitive.Operations] (input : Slice U8)
    (large : 33554432 < input.length) :
    RegistrationNativePacketReadback.decodeInit input = .ok .None := by
  have source := (RegistrationPublicDecoderTotal.init_none_iff input).mpr (by
    rintro ⟨value, _, _, bounded⟩
    omega)
  rw [RegistrationNativePacketReadback.decodeInit, source]
  rfl

theorem response_oversize [RegistrationValidatorPrimitive.Operations] (input : Slice U8)
    (large : 33554432 < input.length) :
    RegistrationNativePacketReadback.decodeResponse input = .ok .None := by
  have source := (RegistrationPublicDecoderTotal.response_none_iff input).mpr (by
    rintro ⟨value, _, _, bounded⟩
    omega)
  rw [RegistrationNativePacketReadback.decodeResponse, source]
  rfl

theorem init_normal [RegistrationValidatorPrimitive.Operations] (bytes : Pqxdh.Bytes)
    (representable : bytes.length ≤ UScalar.max .Usize) :
    ∃ reply : Option registration.InitPacket,
      RegistrationNativePacketReadback.decodeInit (FrameCodecReadBack.inputSlice bytes representable) = .ok reply ∧
      RegistrationNativeSourceWire.decodeInit bytes = reply := by
  obtain ⟨reply, decoded⟩ := init_total (FrameCodecReadBack.inputSlice bytes representable)
  refine ⟨reply, decoded, ?_⟩
  by_cases inside : bytes.length ≤ CborSizing.maxMessageSize
  · rw [RegistrationNativeSourceWire.decodeInit, dite_eq_left inside, decoded]
    cases reply <;> rfl
  · have large : 33554432 < bytes.length := Nat.lt_of_not_ge inside
    have rejected := init_oversize (FrameCodecReadBack.inputSlice bytes representable)
      (by simpa only [FrameCodecReadBack.inputSlice, Slice.length, List.length_map] using large)
    have absent : reply = .None := RustM.ok.inj (decoded.symm.trans rejected)
    rw [absent, RegistrationNativeSourceWire.decodeInit, dite_eq_right inside]

theorem response_normal [RegistrationValidatorPrimitive.Operations] (bytes : Pqxdh.Bytes)
    (representable : bytes.length ≤ UScalar.max .Usize) :
    ∃ reply : Option registration.ResponsePacket,
      RegistrationNativePacketReadback.decodeResponse (FrameCodecReadBack.inputSlice bytes representable) = .ok reply ∧
      RegistrationNativeSourceWire.decodeResponse bytes = reply := by
  obtain ⟨reply, decoded⟩ := response_total (FrameCodecReadBack.inputSlice bytes representable)
  refine ⟨reply, decoded, ?_⟩
  by_cases inside : bytes.length ≤ CborSizing.maxMessageSize
  · rw [RegistrationNativeSourceWire.decodeResponse, dite_eq_left inside, decoded]
    cases reply <;> rfl
  · have large : 33554432 < bytes.length := Nat.lt_of_not_ge inside
    have rejected := response_oversize (FrameCodecReadBack.inputSlice bytes representable)
      (by simpa only [FrameCodecReadBack.inputSlice, Slice.length, List.length_map] using large)
    have absent : reply = .None := RustM.ok.inj (decoded.symm.trans rejected)
    rw [absent, RegistrationNativeSourceWire.decodeResponse, dite_eq_right inside]

theorem init_exact [RegistrationValidatorPrimitive.Operations] (bytes : Pqxdh.Bytes)
    (representable : bytes.length ≤ UScalar.max .Usize) (reply : Option registration.InitPacket)
    (decoded : RegistrationNativePacketReadback.decodeInit (FrameCodecReadBack.inputSlice bytes representable) = .ok reply) :
    RegistrationNativeSourceWire.decodeInit bytes = reply := by
  obtain ⟨actual, normal, facade⟩ := init_normal bytes representable
  have same := RustM.ok.inj (normal.symm.trans decoded)
  simpa only [same] using facade

theorem response_exact [RegistrationValidatorPrimitive.Operations] (bytes : Pqxdh.Bytes)
    (representable : bytes.length ≤ UScalar.max .Usize) (reply : Option registration.ResponsePacket)
    (decoded : RegistrationNativePacketReadback.decodeResponse (FrameCodecReadBack.inputSlice bytes representable) = .ok reply) :
    RegistrationNativeSourceWire.decodeResponse bytes = reply := by
  obtain ⟨actual, normal, facade⟩ := response_normal bytes representable
  have same := RustM.ok.inj (normal.symm.trans decoded)
  simpa only [same] using facade
end BeaconcryptCore.Computational.RegistrationNativeDecoderTotal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDecoderTotal.init_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDecoderTotal.init_total

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDecoderTotal.response_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDecoderTotal.response_total

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDecoderTotal.init_oversize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDecoderTotal.init_oversize

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDecoderTotal.response_oversize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDecoderTotal.response_oversize

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDecoderTotal.init_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDecoderTotal.init_normal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDecoderTotal.response_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDecoderTotal.response_normal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDecoderTotal.init_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDecoderTotal.init_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeDecoderTotal.response_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeDecoderTotal.response_exact

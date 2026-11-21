-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.FrameCodecRoundtrip
import BeaconcryptCore.Refinement.FrameCodecDecodeTotality
import BeaconcryptCore.Refinement.FrameCodecRepresentation
import BeaconcryptCore.Refinement.ProtocolComposition

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_parse PqxdhRefinement
open BeaconcryptCore.Refinement.FrameCodecArgument
open BeaconcryptCore.Refinement.FrameCodecRoundtrip
open BeaconcryptCore.Refinement.FrameCodecRepresentation
open BeaconcryptCore.Refinement.ProtocolComposition (concreteByte absByte_concreteByte)
open BeaconcryptCore.Computational

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.FrameCodecReadBack

/-- Byte conversion is injective in both directions and changes no native byte. -/
theorem concrete_abs_byte (byte : U8) : concreteByte (absByte byte) = byte := by
  apply absByte_injective
  exact absByte_concreteByte (absByte byte)

theorem concrete_abs_bytes (bytes : List U8) :
    (bytes.map absByte).map concreteByte = bytes := by
  simp [List.map_map, Function.comp_def, concrete_abs_byte]

def inputSlice (bytes : Pqxdh.Bytes) (bound : bytes.length ≤ UScalar.max .Usize) : Slice U8 :=
  ⟨bytes.map concreteByte, by simpa only [List.length_map, UScalar.max_USize_eq] using bound⟩

/-- A byte view of the actual extracted native parser, with the same inclusive complete-message bound. The checked decoder totality theorem covers hostile inputs too; nativeDecode_normal identifies the facade with its ordinary optional reply. -/
noncomputable def nativeDecode (bytes : Pqxdh.Bytes) : Option RawCtxReceive.DecodedFrame :=
  if inside : bytes.length ≤ 33554432 then
    match frame.decode (inputSlice bytes (inside.trans BeaconcryptCore.Refinement.Transport.message_limit_representable)) with
    | .ok (.Some parsed) => some (⟨parsed.seq, parsed.key_id, parsed.cipher_text.val.map absByte⟩ : RawCtxReceive.DecodedFrame)
    | _ => none
  else none

/-- The decoder rejects oversized wire messages without requiring any parser law. -/
theorem nativeDecode_oversize (bytes : Pqxdh.Bytes) (large : 33554432 < bytes.length) :
    nativeDecode bytes = none := by
  rw [nativeDecode, dite_eq_right (Nat.not_le_of_lt large)]

/-- Every native byte slice returns normally, and the facade maps precisely that optional reply. Error and divergence are impossible even for hostile input. -/
theorem nativeDecode_normal (bytes : Pqxdh.Bytes) (representable : bytes.length ≤ UScalar.max .Usize) :
    ∃ reply : Option frame.Frame, frame.decode (inputSlice bytes representable) = ok reply ∧
      nativeDecode bytes = _root_.Option.map (fun parsed =>
        (⟨parsed.seq, parsed.key_id, parsed.cipher_text.val.map absByte⟩ : RawCtxReceive.DecodedFrame)) reply := by
  obtain ⟨reply, decoded⟩ := FrameCodecDecodeTotality.decode_total (inputSlice bytes representable)
  refine ⟨reply, decoded, ?_⟩
  by_cases inside : bytes.length ≤ 33554432
  · unfold nativeDecode
    rw [dite_eq_left inside, decoded]
    cases reply <;> rfl
  · have large : 33554432 < bytes.length := Nat.lt_of_not_ge inside
    have rejected := decode_oversize (inputSlice bytes representable)
      (by simpa only [inputSlice, List.length_map] using large)
    have absent : reply = .None := RustM.ok.inj (decoded.symm.trans rejected)
    rw [absent, nativeDecode_oversize bytes large]
    rfl

/-- A normal extracted decoder result is exactly the facade's result, with only the byte representation converted. -/
theorem nativeDecode_exact (bytes : Pqxdh.Bytes) (representable : bytes.length ≤ UScalar.max .Usize)
    (reply : Option frame.Frame) (decoded : frame.decode (inputSlice bytes representable) = ok reply) :
    nativeDecode bytes = _root_.Option.map (fun parsed =>
      (⟨parsed.seq, parsed.key_id, parsed.cipher_text.val.map absByte⟩ : RawCtxReceive.DecodedFrame)) reply := by
  obtain ⟨actual, normal, facade⟩ := nativeDecode_normal bytes representable
  have same : actual = reply := RustM.ok.inj (normal.symm.trans decoded)
  simpa only [same] using facade

abbrev ArgumentDecoder := ∀ (major : U8) (value : U64), (major = 0#u8 ∨ major = 2#u8) →
  ∀ (input : Slice U8) (rest : List U8), input.val = argumentBytes major value ++ rest →
    frame.decode_argument input major = ok (.Some (value, (encoded major value).length))

/-- The concrete parser reads the model's rendered native frame exactly; only the scalar component theorem remains to be instantiated. -/
theorem native_render_of_arguments (argumentDecoder : ArgumentDecoder)
    (sequence sender : U64) (payload : Slice U8)
    (fits : (frameBytes sequence sender payload).length ≤ 33554432) :
    nativeDecode (CborTransport.render ⟨sequence, sender, payload.val.map absByte⟩) =
      some ⟨sequence, sender, payload.val.map absByte⟩ := by
  rw [← frame_abs]
  have inside : ((frameBytes sequence sender payload).map absByte).length ≤ 33554432 := by
    simpa only [List.length_map] using fits
  unfold nativeDecode
  rw [dite_eq_left inside]
  let input := inputSlice ((frameBytes sequence sender payload).map absByte)
    (inside.trans BeaconcryptCore.Refinement.Transport.message_limit_representable)
  have view : input.val = frameBytes sequence sender payload := by
    exact concrete_abs_bytes _
  have decoded := decode_roundtrip_of_arguments argumentDecoder input payload sequence sender
    (by simpa only [view] using fits) (by simpa only [frameBytes] using view)
  change (match frame.decode input with
    | .ok (.Some parsed) => some (⟨parsed.seq, parsed.key_id, parsed.cipher_text.val.map absByte⟩ : RawCtxReceive.DecodedFrame)
    | _ => none) = _
  rw [decoded]

/-- Every representable logical payload is no larger than its complete canonical frame. -/
theorem payload_le_render (frame : RawCtxReceive.DecodedFrame)
    (representable : frame.payload.length < 2 ^ 64) :
    frame.payload.length ≤ (CborTransport.render frame).length := by
  rw [CborTransport.render_length frame representable]
  simp only [CborSizing.frameLen, CborSizing.byteStringLen]
  omega

/-- Read-back for every bounded representable logical frame, obtained through the actual native parser. -/
theorem render_readback_of_arguments (argumentDecoder : ArgumentDecoder)
    (frame : RawCtxReceive.DecodedFrame)
    (representable : frame.payload.length < 2 ^ 64)
    (fits : (CborTransport.render frame).length ≤ 33554432) :
    nativeDecode (CborTransport.render frame) = some frame := by
  let payload := inputSlice frame.payload
    (((payload_le_render frame representable).trans fits).trans
      BeaconcryptCore.Refinement.Transport.message_limit_representable)
  have payloadView : payload.val.map absByte = frame.payload := by
    change (frame.payload.map concreteByte).map absByte = frame.payload
    simp [List.map_map, Function.comp_def, absByte_concreteByte]
  have wireLength : (frameBytes frame.sequence frame.sender payload).length =
      (CborTransport.render frame).length := by
    simpa only [List.length_map, payloadView] using
      congrArg List.length (frame_abs frame.sequence frame.sender payload)
  simpa only [payloadView] using
    native_render_of_arguments argumentDecoder frame.sequence frame.sender payload (by simpa only [wireLength] using fits)

/-- The scalar inverse is discharged by the checked extracted-code theorem, not a parser assumption. -/
theorem native_render (sequence sender : U64) (payload : Slice U8)
    (fits : (frameBytes sequence sender payload).length ≤ 33554432) :
    nativeDecode (CborTransport.render ⟨sequence, sender, payload.val.map absByte⟩) =
      some ⟨sequence, sender, payload.val.map absByte⟩ := by
  exact native_render_of_arguments decode_argument_roundtrip sequence sender payload fits

/-- Concrete ordinary-frame read-back discharges the model's codec obligation on its admitted domain. -/
theorem render_readback (frame : RawCtxReceive.DecodedFrame)
    (representable : frame.payload.length < 2 ^ 64)
    (fits : (CborTransport.render frame).length ≤ 33554432) :
    nativeDecode (CborTransport.render frame) = some frame := by
  exact render_readback_of_arguments decode_argument_roundtrip frame representable fits

end BeaconcryptCore.Refinement.FrameCodecReadBack

/-- info: 'BeaconcryptCore.Refinement.FrameCodecReadBack.concrete_abs_byte' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecReadBack.concrete_abs_byte

/-- info: 'BeaconcryptCore.Refinement.FrameCodecReadBack.concrete_abs_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecReadBack.concrete_abs_bytes

/-- info: 'BeaconcryptCore.Refinement.FrameCodecReadBack.nativeDecode_oversize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecReadBack.nativeDecode_oversize

/-- info: 'BeaconcryptCore.Refinement.FrameCodecReadBack.nativeDecode_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecReadBack.nativeDecode_normal

/-- info: 'BeaconcryptCore.Refinement.FrameCodecReadBack.nativeDecode_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecReadBack.nativeDecode_exact

/-- info: 'BeaconcryptCore.Refinement.FrameCodecReadBack.native_render_of_arguments' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecReadBack.native_render_of_arguments

/-- info: 'BeaconcryptCore.Refinement.FrameCodecReadBack.payload_le_render' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecReadBack.payload_le_render

/-- info: 'BeaconcryptCore.Refinement.FrameCodecReadBack.render_readback_of_arguments' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecReadBack.render_readback_of_arguments

/-- info: 'BeaconcryptCore.Refinement.FrameCodecReadBack.native_render' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecReadBack.native_render

/-- info: 'BeaconcryptCore.Refinement.FrameCodecReadBack.render_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecReadBack.render_readback

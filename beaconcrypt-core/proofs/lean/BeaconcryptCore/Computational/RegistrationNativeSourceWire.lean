-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePacketReadback
import BeaconcryptCore.Refinement.FrameCodecReadBack
import BeaconcryptCore.Refinement.AdapterWireVector
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
/-! A serialization representation built by running the actual buffer-taking public codecs on mathematical capacity buffers. Runtime allocation, its failures and its poststate remain in the separately extracted stateful writer; no equality erasing that allocation is asserted. Decoder operations are explicit parameters; readback holds for every interpretation of those private branches. Their irrelevance on every hostile input is a separate obligation. Frame fields are supplied independently. -/
namespace BeaconcryptCore.Computational.RegistrationNativeSourceWire
open BeaconcryptCore.Refinement RegistrationNativeSourceEncoders
open RegistrationSerializerReachableSource
open ProtocolComposition (concreteByte)

def buffer (length : Nat) (bound : length ≤ UScalar.max .Usize) : Slice U8 :=
  ⟨List.replicate length 0#u8, by simpa only [List.length_replicate, UScalar.max_USize_eq] using bound⟩

def encodedBytes (result : RustM (Usize × Slice U8)) : core.option.Option Pqxdh.Bytes :=
  match result with
  | .ok (written, after) => if written = 0#usize then .None else .Some (after.val.map absByte)
  | _ => .None

def encodeInit (other : OtherBranches) (view : registration.SignedInitView) : core.option.Option Pqxdh.Bytes :=
  encodedBytes (RegistrationNativeSourceEncoders.encodeInit other view
    (buffer 6757 (by scalar_tac)))

def encodeResponse (other : OtherBranches) (view : registration.SignedResponseView) : core.option.Option Pqxdh.Bytes :=
  if admitted : RegistrationSerializerResponseBytes.totalLength (responseSyntax view) ≤ CborSizing.maxMessageSize then
    encodedBytes (RegistrationNativeSourceEncoders.encodeResponse other view
      (buffer (RegistrationSerializerResponseBytes.totalLength (responseSyntax view))
        (admitted.trans Transport.message_limit_representable)))
  else .None

def decodeInit [RegistrationValidatorPrimitive.Operations] (bytes : Pqxdh.Bytes) : Option registration.InitPacket :=
  if admitted : bytes.length ≤ CborSizing.maxMessageSize then
    match RegistrationNativePacketReadback.decodeInit
      (FrameCodecReadBack.inputSlice bytes (admitted.trans Transport.message_limit_representable)) with
    | .ok (.Some packet) => some packet
    | _ => none
  else none

def decodeResponse [RegistrationValidatorPrimitive.Operations] (bytes : Pqxdh.Bytes) : Option registration.ResponsePacket :=
  if admitted : bytes.length ≤ CborSizing.maxMessageSize then
    match RegistrationNativePacketReadback.decodeResponse
      (FrameCodecReadBack.inputSlice bytes (admitted.trans Transport.message_limit_representable)) with
    | .ok (.Some packet) => some packet
    | _ => none
  else none

def wire [RegistrationValidatorPrimitive.Operations] (other : OtherBranches)
    (parseFrame : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame)
    (frameWrite : RawCtxMixedShared.Writer) : RegistrationNativeWire.Wire where
  decodeInit := decodeInit
  encodeInit := encodeInit other
  decodeResponse := decodeResponse
  encodeResponse := encodeResponse other
  parseFrame := parseFrame
  frameWrite := frameWrite

theorem init_encoded (other : OtherBranches) (view : registration.SignedInitView) :
    encodeInit other view = .Some ((136#u8 :: RegistrationSerializerInitBytes.payload (initSyntax view)).map absByte) := by
  let output := buffer 6757 (by scalar_tac)
  obtain ⟨after, encoded, _, bytes⟩ := RegistrationNativeSourceEncoders.init_bytes other view output (by simp only [output, buffer, Slice.length, List.length_replicate, Nat.le_refl])
  have afterBytes : after.val = 136#u8 :: RegistrationSerializerInitBytes.payload (initSyntax view) := by
    simpa only [output, buffer, List.drop_replicate, Nat.sub_self, List.replicate_zero, List.append_nil] using bytes
  unfold encodeInit
  change encodedBytes (RegistrationNativeSourceEncoders.encodeInit other view output) = _
  rw [encoded]
  simp only [encodedBytes, afterBytes, show ¬ (6757#usize = 0#usize) by decide, ↓reduceIte]

theorem response_encoded (other : OtherBranches) (view : registration.SignedResponseView)
    (admitted : RegistrationSerializerResponseBytes.totalLength (responseSyntax view) ≤ CborSizing.maxMessageSize) :
    encodeResponse other view = .Some ((136#u8 :: RegistrationSerializerResponseBytes.payload (responseSyntax view)).map absByte) := by
  let output := buffer (RegistrationSerializerResponseBytes.totalLength (responseSyntax view))
    (admitted.trans Transport.message_limit_representable)
  obtain ⟨after, encoded, _, bytes, cursor⟩ := RegistrationNativeSourceEncoders.response_bytes other view output
    (by simp only [output, buffer, Slice.length, List.length_replicate, Nat.le_refl]) admitted
  have afterBytes : after.val = 136#u8 :: RegistrationSerializerResponseBytes.payload (responseSyntax view) := by
    simpa only [output, buffer, List.drop_replicate, Nat.sub_self, List.replicate_zero, List.append_nil] using bytes
  have nonzero : RegistrationSerializerResponseBytes.finalCursor (responseSyntax view) ≠ 0#usize := by
    intro zero
    have := congrArg UScalar.val zero
    rw [cursor] at this
    change RegistrationSerializerResponseBytes.totalLength (responseSyntax view) = 0 at this
    unfold RegistrationSerializerResponseBytes.totalLength at this
    omega
  rw [encodeResponse, dite_eq_left admitted]
  change encodedBytes (RegistrationNativeSourceEncoders.encodeResponse other view output) = _
  rw [encoded]
  simp only [encodedBytes, afterBytes, nonzero, ↓reduceIte]

set_option backward.isDefEq.respectTransparency false in
theorem init_readback [RegistrationValidatorPrimitive.Operations]
    (other : OtherBranches) (parseFrame : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame)
    (frameWrite : RawCtxMixedShared.Writer) :
    RegistrationNativeWire.InitReadBack (wire other parseFrame frameWrite) := by
  intro view bytes encoded
  change encodeInit other view = .Some bytes at encoded
  rw [init_encoded] at encoded
  injection encoded with same
  subst bytes
  have length : ((136#u8 :: RegistrationSerializerInitBytes.payload (initSyntax view)).map absByte).length = 6757 := by
    simp only [List.length_map, List.length_cons, RegistrationPublicReadback.init_payload_length _ (init_shape view)]
  have admitted : ((136#u8 :: RegistrationSerializerInitBytes.payload (initSyntax view)).map absByte).length ≤ CborSizing.maxMessageSize := by rw [length]; decide
  simp only [RegistrationNativeWire.readInit, wire, admitted, ↓reduceIte]
  rw [decodeInit, dite_eq_left admitted]
  rw [RegistrationNativePacketReadback.init_readback _ view (FrameCodecReadBack.concrete_abs_bytes _)]

set_option backward.isDefEq.respectTransparency false in
theorem response_readback [RegistrationValidatorPrimitive.Operations]
    (other : OtherBranches) (parseFrame : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame)
    (frameWrite : RawCtxMixedShared.Writer) :
    RegistrationNativeWire.ResponseReadBack (wire other parseFrame frameWrite) := by
  intro view bytes encoded
  change encodeResponse other view = .Some bytes at encoded
  by_cases admitted : RegistrationSerializerResponseBytes.totalLength (responseSyntax view) ≤ CborSizing.maxMessageSize
  · rw [response_encoded other view admitted] at encoded
    injection encoded with same
    subst bytes
    have length : ((136#u8 :: RegistrationSerializerResponseBytes.payload (responseSyntax view)).map absByte).length =
        RegistrationSerializerResponseBytes.totalLength (responseSyntax view) := by
      simp only [List.length_map, List.length_cons]
      exact RegistrationPublicReadback.response_payload_length _ (response_shape view)
    have fit : ((136#u8 :: RegistrationSerializerResponseBytes.payload (responseSyntax view)).map absByte).length ≤ CborSizing.maxMessageSize := length ▸ admitted
    simp only [RegistrationNativeWire.readResponse, wire, fit, ↓reduceIte]
    rw [decodeResponse, dite_eq_left fit]
    rw [RegistrationNativePacketReadback.response_readback _ view (FrameCodecReadBack.concrete_abs_bytes _) admitted]
  · rw [encodeResponse, dite_eq_right admitted] at encoded
    contradiction
end BeaconcryptCore.Computational.RegistrationNativeSourceWire

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceWire.init_encoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceWire.init_encoded

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceWire.response_encoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceWire.response_encoded

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceWire.init_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceWire.init_readback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceWire.response_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceWire.response_readback

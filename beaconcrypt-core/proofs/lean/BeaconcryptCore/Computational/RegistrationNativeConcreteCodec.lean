-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeDecoderTotal
import BeaconcryptCore.Computational.RegistrationNativeSourceWriterReadback
import BeaconcryptCore.Refinement.FrameCodecContracts
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
/-! A concrete byte representation using the actual source-backed registration codecs and frame codec. Private text/map and non-registration serializer branches are assigned failing effects. All-input decoder independence and typed serializer reachability make these choices irrelevant, rather than imposing codec laws. Mathematical output buffers are a serialization representation; runtime reservation, allocation failure and mutable poststate remain in the actual source writer programs. -/
namespace BeaconcryptCore.Computational.RegistrationNativeConcreteCodec
open BeaconcryptCore.Refinement
open RegistrationSerializerReachableSource

@[instance_reducible] def decoderOperations : RegistrationValidatorPrimitive.Operations where
  utf8Correct _ := .fail .panic
  sortedMap _ _ _ := .fail .panic

def serializerBranches : OtherBranches where
  deepSerialize _ _ _ := .fail .panic
  otherSerialize _ _ _ := .fail .panic
  deepSize _ _ := .fail .panic
  otherSize _ _ := .fail .panic
  textFactory _ := .fail .panic
  utf8Correct _ := .fail .panic

/-- This binding exposes the actual buffer-taking source encoders, with complete returned slices. -/
@[instance_reducible] def writerOperations : RegistrationWriterPrimitive.Operations :=
  RegistrationNativeSourceEncoders.sourceOperations serializerBranches

noncomputable def parseFrame (bytes : Pqxdh.Bytes) : Option CborProductionBoundary.NativeFrame :=
  if admitted : bytes.length ≤ CborSizing.maxMessageSize then
    match beaconcrypt_parse.frame.decode (FrameCodecReadBack.inputSlice bytes
      (admitted.trans Transport.message_limit_representable)) with
    | .ok (.Some parsed) => some ⟨parsed.seq, parsed.key_id, parsed.cipher_text⟩
    | _ => none
  else none

noncomputable def wire : RegistrationNativeWire.Wire :=
  @RegistrationNativeSourceWire.wire decoderOperations serializerBranches parseFrame FrameCodecContracts.nativeWrite

theorem init_independent (other : RegistrationValidatorPrimitive.Operations) (input : Slice U8) :
    @RegistrationNativePacketReadback.decodeInit decoderOperations input =
      @RegistrationNativePacketReadback.decodeInit other input := by
  unfold RegistrationNativePacketReadback.decodeInit
  rw [RegistrationDecoderBranchIndependence.init_independent decoderOperations other input]

theorem response_independent (other : RegistrationValidatorPrimitive.Operations) (input : Slice U8) :
    @RegistrationNativePacketReadback.decodeResponse decoderOperations input =
      @RegistrationNativePacketReadback.decodeResponse other input := by
  unfold RegistrationNativePacketReadback.decodeResponse
  rw [RegistrationDecoderBranchIndependence.response_independent decoderOperations other input]

theorem init_normal (bytes : Pqxdh.Bytes) (representable : bytes.length ≤ UScalar.max .Usize) :
    ∃ reply : Option registration.InitPacket,
      @RegistrationNativePacketReadback.decodeInit decoderOperations
        (FrameCodecReadBack.inputSlice bytes representable) = .ok reply ∧ wire.decodeInit bytes = reply :=
  @RegistrationNativeDecoderTotal.init_normal decoderOperations bytes representable

theorem response_normal (bytes : Pqxdh.Bytes) (representable : bytes.length ≤ UScalar.max .Usize) :
    ∃ reply : Option registration.ResponsePacket,
      @RegistrationNativePacketReadback.decodeResponse decoderOperations
        (FrameCodecReadBack.inputSlice bytes representable) = .ok reply ∧ wire.decodeResponse bytes = reply :=
  @RegistrationNativeDecoderTotal.response_normal decoderOperations bytes representable

theorem init_readback : RegistrationNativeWire.InitReadBack wire :=
  @RegistrationNativeSourceWire.init_readback decoderOperations serializerBranches parseFrame FrameCodecContracts.nativeWrite

theorem response_readback : RegistrationNativeWire.ResponseReadBack wire :=
  @RegistrationNativeSourceWire.response_readback decoderOperations serializerBranches parseFrame FrameCodecContracts.nativeWrite

theorem init_bytes (view : registration.SignedInitView) :
    wire.encodeInit view = .Some ((136#u8 :: RegistrationSerializerInitBytes.payload
      (RegistrationNativeSourceEncoders.initSyntax view)).map absByte) :=
  RegistrationNativeSourceWire.init_encoded serializerBranches view

theorem response_bytes (view : registration.SignedResponseView)
    (admitted : RegistrationSerializerResponseBytes.totalLength
      (RegistrationNativeSourceEncoders.responseSyntax view) ≤ CborSizing.maxMessageSize) :
    wire.encodeResponse view = .Some ((136#u8 :: RegistrationSerializerResponseBytes.payload
      (RegistrationNativeSourceEncoders.responseSyntax view)).map absByte) :=
  RegistrationNativeSourceWire.response_encoded serializerBranches view admitted

theorem frame_projection (bytes : Pqxdh.Bytes) :
    CborProductionBoundary.decoded <$> wire.parseFrame bytes = FrameCodecReadBack.nativeDecode bytes := by
  change CborProductionBoundary.decoded <$> parseFrame bytes = _
  unfold parseFrame FrameCodecReadBack.nativeDecode CborSizing.maxMessageSize
  by_cases admitted : bytes.length ≤ 33554432
  · rw [dite_eq_left admitted, dite_eq_left admitted]
    cases beaconcrypt_parse.frame.decode
      (FrameCodecReadBack.inputSlice bytes (admitted.trans Transport.message_limit_representable)) with
    | ok reply => cases reply <;> rfl
    | fail error => rfl
    | div => rfl
  · rw [dite_eq_right admitted, dite_eq_right admitted]
    rfl

theorem frame_normal (bytes : Pqxdh.Bytes) (representable : bytes.length ≤ UScalar.max .Usize) :
    ∃ reply : Option beaconcrypt_parse.frame.Frame,
      beaconcrypt_parse.frame.decode (FrameCodecReadBack.inputSlice bytes representable) = .ok reply ∧
      wire.parseFrame bytes = (fun parsed => (⟨parsed.seq, parsed.key_id, parsed.cipher_text⟩ : CborProductionBoundary.NativeFrame)) <$> reply := by
  obtain ⟨reply, normal⟩ := FrameCodecDecodeTotality.decode_total (FrameCodecReadBack.inputSlice bytes representable)
  refine ⟨reply, normal, ?_⟩
  change parseFrame bytes = _
  unfold parseFrame
  by_cases admitted : bytes.length ≤ CborSizing.maxMessageSize
  · rw [dite_eq_left admitted, normal]
    cases reply <;> rfl
  · have rejected := FrameCodecRoundtrip.decode_oversize (FrameCodecReadBack.inputSlice bytes representable)
      (by simpa only [FrameCodecReadBack.inputSlice, List.length_map, CborSizing.maxMessageSize] using Nat.lt_of_not_ge admitted)
    have absent := RustM.ok.inj (normal.symm.trans rejected)
    rw [dite_eq_right admitted, absent]
    rfl

theorem writer_init (value : beaconcrypt_parse.transport.initkex) (output : Slice U8) :
    writerOperations.encodeInit value output =
      @beaconcrypt_parse.extraction_encode_init (RegistrationSerializerReachableSource.operations serializerBranches) value output := rfl

theorem writer_response (value : beaconcrypt_parse.transport.kexresponse) (output : Slice U8) :
    writerOperations.encodeResponse value output =
      @beaconcrypt_parse.extraction_encode_response (RegistrationSerializerReachableSource.operations serializerBranches) value output := rfl
end BeaconcryptCore.Computational.RegistrationNativeConcreteCodec

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeConcreteCodec.init_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeConcreteCodec.init_independent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeConcreteCodec.response_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeConcreteCodec.response_independent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeConcreteCodec.init_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeConcreteCodec.init_normal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeConcreteCodec.response_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeConcreteCodec.response_normal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeConcreteCodec.init_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeConcreteCodec.init_readback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeConcreteCodec.response_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeConcreteCodec.response_readback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeConcreteCodec.init_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeConcreteCodec.init_bytes

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeConcreteCodec.response_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeConcreteCodec.response_bytes

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeConcreteCodec.frame_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeConcreteCodec.frame_projection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeConcreteCodec.frame_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeConcreteCodec.frame_normal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeConcreteCodec.writer_init' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeConcreteCodec.writer_init

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeConcreteCodec.writer_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeConcreteCodec.writer_response

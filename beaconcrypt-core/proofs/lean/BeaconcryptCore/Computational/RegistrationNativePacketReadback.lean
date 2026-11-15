-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSourceEncoders
import BeaconcryptCore.Refinement.RegistrationPublicReadback
import BeaconcryptCore.Refinement.RegistrationInputs
import BeaconcryptCore.Computational.RegistrationNativeWire
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
/-! Native packet decoding composes the actual public parser with the actual extracted fixed-width packet constructors. All four Init fields and all Response fields including the complete application slice survive this composition. -/
namespace BeaconcryptCore.Computational.RegistrationNativePacketReadback
open BeaconcryptCore.Refinement RegistrationNativeSourceEncoders

def decodeInit [RegistrationValidatorPrimitive.Operations] (input : Slice U8) : RustM (core.option.Option registration.InitPacket) := do
  let parsed ← beaconcrypt_parse.extraction_decode_init input
  match parsed with
  | .None => .ok .None
  | .Some value => registration.InitPacket.from_slices value.identity_key value.pre_key value.one_time_key value.pq_key

def decodeResponse [RegistrationValidatorPrimitive.Operations] (input : Slice U8) : RustM (core.option.Option registration.ResponsePacket) := do
  let parsed ← beaconcrypt_parse.extraction_decode_response input
  match parsed with
  | .None => .ok .None
  | .Some value => registration.ResponsePacket.from_slices value.identity_key value.ephemeral_key value.kem_cipher_text value.key_id value.app_cipher_text value.signature

theorem borrowed_array {size : Usize} (array : Array U8 size) :
    core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from size array.to_slice = .ok (.Ok array) := by
  obtain ⟨result, run, facts⟩ := RegistrationInputs.borrowed_slice_exact size array.to_slice
  cases result with
  | Err error => exact False.elim (facts array.property)
  | Ok output =>
    have same : output = array := Subtype.ext facts.1
    simpa only [same] using run

theorem copied_array {size : Usize} (array : Array U8 size) :
    core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from size core.U8.Insts.CoreMarkerCopy array.to_slice = .ok (.Ok array) := by
  obtain ⟨result, run, facts⟩ := RegistrationInputs.copied_slice_exact size array.to_slice
  cases result with
  | Err error => exact False.elim (facts array.property)
  | Ok output =>
    have same : output = array := Subtype.ext facts.1
    simpa only [same] using run

theorem init_packet (view : registration.InitView) :
    registration.InitPacket.from_slices (initSyntax view).identity_key (initSyntax view).pre_key
      (initSyntax view).one_time_key (initSyntax view).pq_key = .ok (.Some (RegistrationNativeWire.initPacket view)) := by
  simp only [registration.InitPacket.from_slices, initSyntax, borrowed_array, bind_tc_ok]
  rfl

theorem response_packet (view : registration.SignedResponseView) :
    registration.ResponsePacket.from_slices (responseSyntax view).identity_key (responseSyntax view).ephemeral_key
      (responseSyntax view).kem_cipher_text (responseSyntax view).key_id (responseSyntax view).app_cipher_text
      (responseSyntax view).signature = .ok (.Some (RegistrationNativeWire.responsePacket view)) := by
  simp only [registration.ResponsePacket.from_slices, responseSyntax, copied_array, borrowed_array, bind_tc_ok]
  rfl

theorem init_readback [RegistrationValidatorPrimitive.Operations] (input : Slice U8)
    (view : registration.InitView)
    (contents : input.val = 134#u8 :: RegistrationSerializerInitBytes.payload (initSyntax view)) :
    decodeInit input = .ok (.Some (RegistrationNativeWire.initPacket view)) := by
  rw [decodeInit, RegistrationPublicReadback.decode_init input (initSyntax view) contents (init_shape view)]
  simp only [bind_tc_ok, init_packet]

theorem response_readback [RegistrationValidatorPrimitive.Operations] (input : Slice U8)
    (view : registration.SignedResponseView)
    (contents : input.val = 136#u8 :: RegistrationSerializerResponseBytes.payload (responseSyntax view))
    (admitted : RegistrationSerializerResponseBytes.totalLength (responseSyntax view) ≤ CborSizing.maxMessageSize) :
    decodeResponse input = .ok (.Some (RegistrationNativeWire.responsePacket view)) := by
  rw [decodeResponse, RegistrationPublicReadback.decode_response input (responseSyntax view) contents (response_shape view) admitted]
  simp only [bind_tc_ok, response_packet]
end BeaconcryptCore.Computational.RegistrationNativePacketReadback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePacketReadback.borrowed_array' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePacketReadback.borrowed_array

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePacketReadback.copied_array' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePacketReadback.copied_array

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePacketReadback.init_packet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePacketReadback.init_packet

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePacketReadback.response_packet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePacketReadback.response_packet

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePacketReadback.init_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePacketReadback.init_readback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePacketReadback.response_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePacketReadback.response_readback

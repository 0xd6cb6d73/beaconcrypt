-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RawCtxFrameDecoding
import BeaconcryptCore.Computational.CborSizing

/-!
The transport boundary after the CBOR migration. Lengths follow `beaconcrypt-parse/src/sizing.rs`; the parser itself remains a functional library boundary. The full decoder is called before the Server can obtain a sender. Registration payloads carry no frame metadata: sequence one and the pinned Server identifier are supplied by the caller.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborTransport
open CborSizing

/-- Pure big-endian argument bytes; this value construction has no native allocator callback. -/
def bigEndian (width value : Nat) : Pqxdh.Bytes :=
  (List.range width).reverse.map fun offset => UInt8.ofNat (value / 256 ^ offset % 256)

def argument (major value : Nat) : Pqxdh.Bytes :=
  if value ≤ 23 then [UInt8.ofNat (32 * major + value)]
  else if value ≤ 255 then UInt8.ofNat (32 * major + 24) :: bigEndian 1 value
  else if value ≤ 65_535 then UInt8.ofNat (32 * major + 25) :: bigEndian 2 value
  else if value ≤ 4_294_967_295 then UInt8.ofNat (32 * major + 26) :: bigEndian 4 value
  else UInt8.ofNat (32 * major + 27) :: bigEndian 8 value

/-- The canonical mathematical CBOR frame. The empty fallback applies only outside CBOR's representable byte-string lengths; there is no allocation or message-limit failure. -/
def render (frame : RawCtxReceive.DecodedFrame) : Pqxdh.Bytes :=
  if frame.payload.length < 2 ^ 64 then
    [0x85, 1, 2] ++ argument 0 frame.sequence.val ++ argument 0 frame.sender.val ++
      argument 2 frame.payload.length ++ frame.payload
  else []

theorem bigEndian_length (width value : Nat) : (bigEndian width value).length = width := by
  simp [bigEndian]

theorem argument_length (major value : Nat) : (argument major value).length = argumentLen value := by
  simp [argument, argumentLen]
  split_ifs
  all_goals simp [bigEndian_length]

/-- Pure rendering has exactly the native canonical frame size whenever CBOR can represent the payload length. -/
theorem render_length (frame : RawCtxReceive.DecodedFrame)
    (representable : frame.payload.length < 2 ^ 64) :
    (render frame).length = frameLen frame.sequence.val frame.sender.val frame.payload.length := by
  rw [render, ite_eq_left representable]
  simp [argument_length, frameLen, byteStringLen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  omega

/-- Obtain routing metadata only after the same complete decoder used to open a frame. -/
def reader (decode : RawCtxReceive.FrameDecoder) :
    RawCtxFrameDecoding.Reader RawCtxReceive.DecodedFrame RawCtxReceive.DecodedFrame where
  readMessage raw := (fun frame => (frame, [])) <$> decode raw
  root := some
  keyId := RawCtxReceive.DecodedFrame.sender
  sequence := RawCtxReceive.DecodedFrame.sequence
  payload frame := some frame.payload

def boundedDecoder (decode : RawCtxReceive.FrameDecoder) : RawCtxReceive.FrameDecoder :=
  fun raw => if raw.length ≤ maxMessageSize then decode raw else none

def registrationFrame (sender : Std.U64) (payload : Pqxdh.Bytes) : RawCtxReceive.DecodedFrame :=
  ⟨1#u64, sender, payload⟩

/-- A native admitted response also admits its pure implicit first-frame representation. -/
theorem registration_render_fits (sender : Std.U64) (payload : Pqxdh.Bytes) (assigned : Nat)
    (admitted : responseLen payload.length assigned ≤ maxMessageSize) :
    (render (registrationFrame sender payload)).length ≤ maxMessageSize := by
  have bound := CborSizing.registration_frame_fits payload.length assigned sender.val admitted
  have representable : payload.length < 2 ^ 64 := by
    unfold frameLen byteStringLen maxMessageSize at bound
    omega
  rw [render_length (registrationFrame sender payload) representable]
  exact bound

theorem registration_render_example :
    render (registrationFrame 0#u64 []) = [0x85, 1, 2, 1, 0, 0x40] := by
  decide

/-- The reader adapter retains every accepted field and every complete-parser rejection. -/
theorem decode_reader (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) :
    RawCtxFrameDecoding.decode (reader decode) raw = decode raw := by
  cases parsed : decode raw <;>
    simp [reader, RawCtxFrameDecoding.decode, RawCtxFrameDecoding.frameRoot,
      RawCtxFrameDecoding.complete, parsed]

/-- Routing succeeds exactly when the same complete decoder has accepted a frame. -/
theorem sender_reader (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) :
    RawCtxFrameDecoding.sender (reader decode) raw =
      RawCtxReceive.DecodedFrame.sender <$> decode raw := by
  cases parsed : decode raw <;>
    simp [reader, RawCtxFrameDecoding.sender, RawCtxFrameDecoding.frameRoot,
      RawCtxFrameDecoding.complete, parsed]

/-- Oversized input is rejected before the supplied native parser is consulted. -/
theorem oversized_decode (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (oversized : maxMessageSize < raw.length) : boundedDecoder decode raw = none := by
  simp [boundedDecoder, Nat.not_le.mpr oversized]

/-- The Server cannot route an oversized or otherwise unparsed frame. -/
theorem oversized_sender (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (oversized : maxMessageSize < raw.length) :
    RawCtxFrameDecoding.sender (reader (boundedDecoder decode)) raw = none := by
  simp [sender_reader, oversized_decode decode raw oversized]

/-- Registration authenticates the raw protected bytes at the implicit first sequence and the pinned Server ID. -/
theorem registration_fields (sender : Std.U64) (payload : Pqxdh.Bytes) :
    (registrationFrame sender payload).sequence = 1#u64 ∧
    (registrationFrame sender payload).sender = sender ∧
    (registrationFrame sender payload).payload = payload := ⟨rfl, rfl, rfl⟩

end BeaconcryptCore.Computational.CborTransport

/-- info: 'BeaconcryptCore.Computational.CborTransport.decode_reader' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTransport.decode_reader
/-- info: 'BeaconcryptCore.Computational.CborTransport.sender_reader' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTransport.sender_reader
/-- info: 'BeaconcryptCore.Computational.CborTransport.oversized_decode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTransport.oversized_decode
/-- info: 'BeaconcryptCore.Computational.CborTransport.oversized_sender' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTransport.oversized_sender
/-- info: 'BeaconcryptCore.Computational.CborTransport.registration_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTransport.registration_fields

/-- info: 'BeaconcryptCore.Computational.CborTransport.bigEndian_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTransport.bigEndian_length
/-- info: 'BeaconcryptCore.Computational.CborTransport.argument_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTransport.argument_length
/-- info: 'BeaconcryptCore.Computational.CborTransport.render_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTransport.render_length
/-- info: 'BeaconcryptCore.Computational.CborTransport.registration_render_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTransport.registration_render_fits
/-- info: 'BeaconcryptCore.Computational.CborTransport.registration_render_example' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTransport.registration_render_example

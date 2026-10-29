-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInterface
import BeaconcryptCore.Computational.CborProductionBoundary
import BeaconcryptCore.Computational.RegistrationWorldServerPublication

/-! The native byte adapter has all six Init fields and the actual dynamically signed response view. Its byte decoders/encoders are the explicit functional SDK codec boundary: the Rust parsers live in beaconcrypt-parse outside the extracted core. The adapter checks the complete 32 MiB bound before calling either decoder. It never replaces native verification with a parsing verdict or supplies an ML signature from a legacy writer. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeWire

structure Wire where
  decodeInit : Pqxdh.Bytes → Option registration.InitPacket
  encodeInit : registration.SignedInitView → core.option.Option Pqxdh.Bytes
  decodeResponse : Pqxdh.Bytes → Option registration.ResponsePacket
  encodeResponse : registration.SignedResponseView → core.option.Option Pqxdh.Bytes
  parseFrame : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame
  frameWrite : RawCtxMixedShared.Writer

/-- All six decoded fixed-width fields are preserved. This is the actual core InitPacket constructor. -/
def initPacket (view : registration.SignedInitView) : registration.InitPacket :=
  ⟨view.fields.identity_key, view.fields.pre_key, view.fields.one_time_key, view.fields.pq_key,
    view.fields.mldsa_public_key, view.signature⟩

def responsePacket (view : registration.SignedResponseView) : registration.ResponsePacket :=
  ⟨⟨view.identity_key, view.ephemeral_key, view.kem_cipher_text, view.key_id⟩,
    view.application_ciphertext, view.signature⟩

def readInit (wire : Wire) (bytes : Pqxdh.Bytes) : Option registration.InitPacket :=
  if bytes.length ≤ CborSizing.maxMessageSize then wire.decodeInit bytes else none

def readResponse (wire : Wire) (bytes : Pqxdh.Bytes) : Option registration.ResponsePacket :=
  if bytes.length ≤ CborSizing.maxMessageSize then wire.decodeResponse bytes else none

/-- Ordinary codec representation contracts for successful actual encodings; failures remain failures. -/
def InitReadBack (wire : Wire) : Prop :=
  ∀ view bytes, wire.encodeInit view = .Some bytes → readInit wire bytes = some (initPacket view)

def ResponseReadBack (wire : Wire) : Prop :=
  ∀ view bytes, wire.encodeResponse view = .Some bytes → readResponse wire bytes = some (responsePacket view)

/-- The ML pin is a separate raw argument, with its actual 1952-byte width check. -/
def parseMldsaPin (bytes : Pqxdh.Bytes) : Option (Std.Array U8 1952#usize) :=
  if width : bytes.length = 1952 then
    some ⟨bytes.map BeaconcryptCore.Refinement.ProtocolComposition.concreteByte, by simpa using width⟩
  else none

/-- Reader-only compatibility for the original CE ledger's public designation. Actual native publication always uses Wire.encodeInit/encodeResponse above, after the genuine signing pipeline. -/
def ledgerCodec (wire : Wire) : PqxdhServerAuthExperiment.Codec registration.InitPacket registration.ResponsePacket where
  read1 := readInit wire
  identity := fun packet => some (absBytes packet.identity_key)
  pqField := fun packet => some (absBytes packet.pq_key)
  preField := fun packet => some (absBytes packet.pre_key)
  oneField := fun packet => some (absBytes packet.one_time_key)
  write1 := fun _ => none
  write2 := fun _ => none
  read2 := readResponse wire
  ciphertext := fun packet => some packet.public.kem_cipher_text
  ephemeral := fun packet => some packet.public.ephemeral_key
  serverIdentity := fun packet => some packet.public.identity_key
  assignedId := fun packet => packet.public.key_id
  application := fun packet => some (TranscriptAuthParts.absSlice packet.application)
  frameRead := CborProductionBoundary.frameDecoder wire.parseFrame
  frameWrite := wire.frameWrite

/-- Oversized raw requests reach no native parser, authentication hash or verifier. -/
theorem read_init_oversized (wire : Wire) (bytes : Pqxdh.Bytes)
    (oversized : CborSizing.maxMessageSize < bytes.length) : readInit wire bytes = none := by
  simp only [readInit, Nat.not_le.mpr oversized, ite_false]

/-- Oversized raw responses reach no native response authentication or receiver. -/
theorem read_response_oversized (wire : Wire) (bytes : Pqxdh.Bytes)
    (oversized : CborSizing.maxMessageSize < bytes.length) : readResponse wire bytes = none := by
  simp only [readResponse, Nat.not_le.mpr oversized, ite_false]

/-- Fixed-width typed Init fields cannot accidentally omit the ML public key or signature. -/
theorem init_packet_fields (view : registration.SignedInitView) :
    (initPacket view).mldsa_public_key = view.fields.mldsa_public_key ∧
      (initPacket view).signature = view.signature := ⟨rfl, rfl⟩

/-- Native pin parsing accepts exactly its required byte width, rather than interpreting an extended pin as the original 32-byte ED pin. -/
theorem parse_mldsa_pin_width (bytes : Pqxdh.Bytes) : (parseMldsaPin bytes).isSome = decide (bytes.length = 1952) := by
  unfold parseMldsaPin
  split <;> simp_all
  rfl

end BeaconcryptCore.Computational.RegistrationNativeWire

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWire.read_init_oversized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWire.read_init_oversized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWire.read_response_oversized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWire.read_response_oversized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWire.init_packet_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWire.init_packet_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeWire.parse_mldsa_pin_width' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeWire.parse_mldsa_pin_width

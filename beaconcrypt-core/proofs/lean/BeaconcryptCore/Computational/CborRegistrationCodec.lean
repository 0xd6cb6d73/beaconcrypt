-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborTransport
import BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl

/-!
CBOR registration uses raw protected payloads. The existing cryptographic experiment uses logical frames, so this codec adapter inserts or removes only that internal representation at the Phase-2 application field. The virtual frame always has sequence one and the pinned Server identifier. Its serialization is proof bookkeeping; it is not an extra wire message or an additional native writer effect.

The explicit laws below separate native Phase-2 read-back, virtual frame read-back, and representability of an admitted payload. They do not assume that raw payloads encode arbitrary frame metadata. Native parser correctness, allocation outcomes and the source-domain size prechecks remain external contracts.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRegistrationCodec
open PqxdhServerAuthExperiment (Codec)
open CborTransport
variable {Reader Response : Type}

def unwrap (decode : RawCtxReceive.FrameDecoder) (sender : Std.U64)
    (bytes : Pqxdh.Bytes) : Option Pqxdh.Bytes := do
  let frame ← decode bytes
  if frame.sequence = 1#u64 ∧ frame.sender = sender then some frame.payload else none

def wrap (sender : Std.U64) (bytes : Pqxdh.Bytes) : Pqxdh.Bytes :=
  render (registrationFrame sender bytes)

/-- Native registration sealing returns the protected bytes directly. Its outer response writer keeps its own optional failure behavior. -/
def raw (codec : Codec Reader Response) : Codec Reader Response :=
  { codec with frameWrite := fun frame => some frame.payload }

theorem raw_frameWrite (codec : Codec Reader Response) (frame : RawCtxReceive.DecodedFrame) :
    (raw codec).frameWrite frame = some frame.payload := by
  rfl

/-- Removing the inner frame does not remove any outer response serialization or parsing failure. -/
theorem raw_outer_codec (codec : Codec Reader Response) :
    (raw codec).write2 = codec.write2 ∧ (raw codec).read2 = codec.read2 := by
  exact ⟨rfl, rfl⟩

/-- This is the codec supplied to the existing experiment, with native wire Phase 2 outside and logical frames inside. -/
def normalize (codec : Codec Reader Response) (sender : Std.U64) : Codec Reader Response :=
  { codec with
    write2 := fun fields => do
      let payload ← unwrap codec.frameRead sender fields.appCiphertext
      codec.write2 { fields with appCiphertext := payload }
    application := fun response => wrap sender <$> codec.application response }

/-- Pure rendered frames of admitted native payloads are accepted by the native parser; this is a parser/size contract, with no writer or allocation success premise. -/
def Representable (codec : Codec Reader Response) (sender : Std.U64) : Prop :=
  ∀ raw response payload, codec.read2 raw = some response → codec.application response = some payload →
    codec.frameRead (wrap sender payload) = some (registrationFrame sender payload)

/-- The virtual representation of a decoded native response is canonical for the logical frame codec. -/
def Stable (codec : Codec Reader Response) : Prop :=
  ∀ virtual frame, codec.frameRead virtual = some frame →
    render frame = virtual

/-- Removing a successfully written virtual first frame recovers exactly the raw protected payload. -/
theorem unwrap_written (codec : Codec Reader Response)
    (readBack : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (sender : Std.U64) (payload virtual : Pqxdh.Bytes)
    (written : codec.frameWrite (registrationFrame sender payload) = some virtual) :
    unwrap codec.frameRead sender virtual = some payload := by
  have parsed := (readBack (registrationFrame sender payload) virtual written).2
  simp [unwrap, parsed, registrationFrame]

/-- An admitted virtual response frame has exactly the implicit metadata and protected payload. -/
theorem unwrap_success (decode : RawCtxReceive.FrameDecoder) (sender : Std.U64)
    (virtual payload : Pqxdh.Bytes) (success : unwrap decode sender virtual = some payload) :
    decode virtual = some (registrationFrame sender payload) := by
  simp only [unwrap, Option.bind_eq_bind, Option.bind_eq_some_iff] at success
  obtain ⟨frame, parsed, admitted⟩ := success
  split_ifs at admitted with metadata
  cases frame; simp_all [registrationFrame]

/-- Native Phase-2 read-back transfers through the virtual canonical representation. -/
theorem phase2_readBack (codec : Codec Reader Response) (sender : Std.U64)
    (native : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (stable : Stable codec) :
    PqxdhServerAuthNegativeControl.Phase2ReadBack (normalize codec sender) := by
  intro fields bytes written
  change (unwrap codec.frameRead sender fields.appCiphertext).bind
    (fun payload => codec.write2 { fields with appCiphertext := payload }) = some bytes at written
  obtain ⟨payload, unwrapped, nativeWritten⟩ := Option.bind_eq_some_iff.mp written
  obtain ⟨response, read, ciphertext, ephemeral, identity, assigned, application⟩ :=
    native { fields with appCiphertext := payload } bytes nativeWritten
  refine ⟨response, read, ciphertext, ephemeral, identity, assigned, ?_⟩
  simpa [normalize, application, wrap] using congrArg some
    (stable fields.appCiphertext (registrationFrame sender payload)
      (unwrap_success codec.frameRead sender fields.appCiphertext payload unwrapped))

/-- Every decoded native response obtains a readable virtual frame; representation cannot silently reject an admitted payload. -/
theorem application_normalized (codec : Codec Reader Response) (sender : Std.U64)
    (representable : Representable codec sender) (raw payload : Pqxdh.Bytes) (response : Response)
    (parsed : codec.read2 raw = some response) (application : codec.application response = some payload) :
    ∃ virtual, (normalize codec sender).application response = some virtual ∧
      codec.frameRead virtual = some (registrationFrame sender payload) := by
  refine ⟨wrap sender payload, ?_, representable raw response payload parsed application⟩
  simp [normalize, application]

/-- Established-session record readers and writers are unchanged by registration normalization. -/
theorem frame_codec_unchanged (codec : Codec Reader Response) (sender : Std.U64) :
    (normalize codec sender).frameRead = codec.frameRead ∧
      (normalize codec sender).frameWrite = codec.frameWrite := ⟨rfl, rfl⟩

/-- Virtual registration framing never consults the optional native frame writer. -/
theorem application_writer_irrelevant (codec : Codec Reader Response) (writer : RawCtxMixedShared.Writer)
    (sender : Std.U64) (response : Response) :
    (normalize { codec with frameWrite := writer } sender).application response =
      (normalize codec sender).application response := rfl

/-- Replacing only the internal raw representation preserves both CTX and AEAD primitive arguments. -/
theorem opening_raw_irrelevant (input : RawCtxWholeOwner.OpenInput) (raw : Pqxdh.Bytes)
    (slices : RawCtxFrameDecoding.Slices) :
    RawCtxSourceOpen.hashInput { input with context := { input.context with raw := raw } } slices =
        RawCtxSourceOpen.hashInput input slices ∧
      RawCtxSourceOpen.baseInput { input with context := { input.context with raw := raw } } slices =
        RawCtxSourceOpen.baseInput input slices := ⟨rfl, rfl⟩

end BeaconcryptCore.Computational.CborRegistrationCodec

/-- info: 'BeaconcryptCore.Computational.CborRegistrationCodec.unwrap_written' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRegistrationCodec.unwrap_written
/-- info: 'BeaconcryptCore.Computational.CborRegistrationCodec.unwrap_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRegistrationCodec.unwrap_success
/-- info: 'BeaconcryptCore.Computational.CborRegistrationCodec.phase2_readBack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRegistrationCodec.phase2_readBack
/-- info: 'BeaconcryptCore.Computational.CborRegistrationCodec.application_normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRegistrationCodec.application_normalized
/-- info: 'BeaconcryptCore.Computational.CborRegistrationCodec.frame_codec_unchanged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRegistrationCodec.frame_codec_unchanged
/-- info: 'BeaconcryptCore.Computational.CborRegistrationCodec.opening_raw_irrelevant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRegistrationCodec.opening_raw_irrelevant

/-- info: 'BeaconcryptCore.Computational.CborRegistrationCodec.application_writer_irrelevant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRegistrationCodec.application_writer_irrelevant

/-- info: 'BeaconcryptCore.Computational.CborRegistrationCodec.raw_frameWrite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRegistrationCodec.raw_frameWrite
/-- info: 'BeaconcryptCore.Computational.CborRegistrationCodec.raw_outer_codec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRegistrationCodec.raw_outer_codec

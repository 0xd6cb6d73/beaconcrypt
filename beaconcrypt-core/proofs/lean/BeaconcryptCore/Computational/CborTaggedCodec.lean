-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRegistrationCodec

/-! A fixed proof codec represents the selected public Server pin in an uncapped eight-byte envelope around native response bytes. The envelope is internal proof data, introduces no native serialization, allocation or cryptographic assumption, and preserves every original byte. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborTaggedCodec
open PqxdhServerAuthExperiment (Codec)
open CborRegistrationCodec CborTransport
variable {Reader Response : Type}

def tag (sender : Std.U64) (raw : Pqxdh.Bytes) : Pqxdh.Bytes :=
  Pqxdh.LE64 sender.val ++ raw

/-- Exact inversion of the fixed public identifier prefix; this mathematical inverse performs no oracle query. -/
noncomputable def untag (bytes : Pqxdh.Bytes) : Option (Std.U64 × Pqxdh.Bytes) := by
  classical
  exact if found : ∃ sender : Std.U64, Pqxdh.LE64 sender.val = bytes.take 8 then
    some (Classical.choose found, bytes.drop 8) else none

theorem sender_encoding_injective (left right : Std.U64)
    (same : Pqxdh.LE64 left.val = Pqxdh.LE64 right.val) : left = right :=
  Std.UScalar.eq_of_val_eq (Pqxdh.LE64_inj left.bv.isLt right.bv.isLt same)

/-- Every identifier and every native response, including an oversized or malformed response, has a total proof representation. -/
theorem untag_tag (sender : Std.U64) (raw : Pqxdh.Bytes) :
    untag (tag sender raw) = some (sender, raw) := by
  have hprefix : (tag sender raw).take 8 = Pqxdh.LE64 sender.val := by
    simp [tag]
  have found : ∃ value : Std.U64, Pqxdh.LE64 value.val = (tag sender raw).take 8 :=
    ⟨sender, hprefix.symm⟩
  have chosen : Classical.choose found = sender :=
    sender_encoding_injective _ _ ((Classical.choose_spec found).trans hprefix)
  simp only [untag, dite_eq_left found, chosen]
  simp [tag]

/-- One fixed codec carries each finish call's public pin in its private response representation. -/
noncomputable def codec (wire : Codec Reader Response) : Codec Reader (Std.U64 × Response) where
  read1 := wire.read1
  identity := wire.identity
  pqField := wire.pqField
  preField := wire.preField
  oneField := wire.oneField
  write1 := wire.write1
  write2 fields := do
    let frame ← wire.frameRead fields.appCiphertext
    if frame.sequence = 1#u64 then do
      let raw ← wire.write2 { fields with appCiphertext := frame.payload }
      some (tag frame.sender raw)
    else none
  read2 bytes := do
    let (sender, raw) ← untag bytes
    let response ← wire.read2 raw
    some (sender, response)
  ciphertext response := wire.ciphertext response.2
  ephemeral response := wire.ephemeral response.2
  serverIdentity response := wire.serverIdentity response.2
  assignedId response := wire.assignedId response.2
  application response := wrap response.1 <$> wire.application response.2
  frameRead := wire.frameRead
  frameWrite := wire.frameWrite

/-- The proof envelope adds eight bytes without imposing a second message-size bound. -/
theorem tag_length (sender : Std.U64) (raw : Pqxdh.Bytes) : (tag sender raw).length = raw.length + 8 := by
  simp [tag, Nat.add_comm]

/-- The fixed response reader recovers the supplied pin and exactly the native optional parse. -/
theorem read_tagged (wire : Codec Reader Response) (sender : Std.U64) (raw : Pqxdh.Bytes) :
    (codec wire).read2 (tag sender raw) = Prod.mk sender <$> wire.read2 raw := by
  cases parsed : wire.read2 raw <;> simp [codec, untag_tag, parsed]

/-- The tagged response uses exactly the dynamic codec's implicit first-frame payload representation. -/
theorem application_tagged (wire : Codec Reader Response) (sender : Std.U64) (response : Response) :
    (codec wire).application (sender, response) =
      (CborRegistrationCodec.normalize wire sender).application response := rfl

/-- A source first-frame writer differs only by the total public envelope around its native response. -/
theorem write_tagged (wire : Codec Reader Response) (sender : Std.U64)
    (fields : PqxdhServerRegistrationPublication.ResponseFields) (frame : RawCtxReceive.DecodedFrame)
    (parsed : wire.frameRead fields.appCiphertext = some frame)
    (first : frame.sequence = 1#u64) (pinned : frame.sender = sender) :
    (codec wire).write2 fields = tag sender <$> (normalize wire sender).write2 fields := by
  simp [codec, CborRegistrationCodec.normalize, unwrap, parsed, first, pinned]
  cases wire.write2 { fields with appCiphertext := frame.payload } <;> rfl

/-- Native Phase-2 read-back remains valid at the fixed tagged codec. -/
theorem phase2_readBack (wire : Codec Reader Response)
    (native : PqxdhServerAuthNegativeControl.Phase2ReadBack wire)
    (stable : CborRegistrationCodec.Stable wire) :
    PqxdhServerAuthNegativeControl.Phase2ReadBack (codec wire) := by
  intro fields bytes written
  simp only [codec, Option.bind_eq_bind, Option.bind_eq_some_iff] at written
  obtain ⟨frame, parsed, written⟩ := written
  split_ifs at written with first
  obtain ⟨raw, nativeWritten, encoded⟩ := Option.bind_eq_some_iff.mp written
  cases Option.some.inj encoded
  obtain ⟨response, read, ciphertext, ephemeral, identity, assigned, application⟩ :=
    native { fields with appCiphertext := frame.payload } raw nativeWritten
  refine ⟨(frame.sender, response), ?_, ciphertext, ephemeral, identity, assigned, ?_⟩
  · simp [read_tagged, read]
  · simpa [codec, application, wrap, registrationFrame, ← first] using
      congrArg some (stable fields.appCiphertext frame parsed)

/-- Native decoded inputs obtain exactly the fixed tagged response and the dynamic readable first frame. -/
theorem admitted_input (wire : Codec Reader Response) (sender : Std.U64)
    (representable : CborRegistrationCodec.Representable wire sender)
    (raw payload : Pqxdh.Bytes) (response : Response)
    (parsed : wire.read2 raw = some response) (application : wire.application response = some payload) :
    ∃ virtual, (codec wire).read2 (tag sender raw) = some (sender, response) ∧
      (codec wire).application (sender, response) = some virtual ∧
      wire.frameRead virtual = some (registrationFrame sender payload) := by
  obtain ⟨virtual, normalized, decoded⟩ := CborRegistrationCodec.application_normalized
    wire sender representable raw payload response parsed application
  refine ⟨virtual, ?_, (application_tagged wire sender response).trans normalized, decoded⟩
  simp [read_tagged, parsed]

end BeaconcryptCore.Computational.CborTaggedCodec

/-- info: 'BeaconcryptCore.Computational.CborTaggedCodec.sender_encoding_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedCodec.sender_encoding_injective
/-- info: 'BeaconcryptCore.Computational.CborTaggedCodec.untag_tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedCodec.untag_tag
/-- info: 'BeaconcryptCore.Computational.CborTaggedCodec.tag_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedCodec.tag_length
/-- info: 'BeaconcryptCore.Computational.CborTaggedCodec.read_tagged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedCodec.read_tagged
/-- info: 'BeaconcryptCore.Computational.CborTaggedCodec.application_tagged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedCodec.application_tagged
/-- info: 'BeaconcryptCore.Computational.CborTaggedCodec.write_tagged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedCodec.write_tagged
/-- info: 'BeaconcryptCore.Computational.CborTaggedCodec.phase2_readBack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedCodec.phase2_readBack
/-- info: 'BeaconcryptCore.Computational.CborTaggedCodec.admitted_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborTaggedCodec.admitted_input

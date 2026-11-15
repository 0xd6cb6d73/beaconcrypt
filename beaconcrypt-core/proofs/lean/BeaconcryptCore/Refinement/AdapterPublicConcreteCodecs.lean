-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicFinishBody
import BeaconcryptCore.Computational.RegistrationNativeConcreteCodec
/-! The concrete actual registration parsers instantiate the public wrapper codec dictionary. Actual source Response Option.and_then and literal Core packet construction equal the source-backed native Wire on every source slice, including malformed and oversized inputs. The proof retains the original borrowed fields and uses proved all-input decoder normality, rather than a codec premise. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicConcreteCodecs
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (liftRust)
open BeaconcryptCore.Computational
variable {m : Type → Type} [Monad m] [LawfulMonad m]

@[instance_reducible] def codecs : Codecs (RustT m) where
  decodeInit input := liftRust (@beaconcrypt_parse.extraction_decode_init RegistrationNativeConcreteCodec.decoderOperations input)
  decodeResponse input := liftRust (@beaconcrypt_parse.extraction_decode_response RegistrationNativeConcreteCodec.decoderOperations input)


def responsePacket (input : Slice U8) : RustT m (Option registration.ResponsePacket) := do
  let parsed ← @Codecs.decodeResponse (RustT m) (codecs (m := m)) input
  AdapterPublicWrapperRequestMonad.Option.and_then
    beaconcrypt_public_request.beacon.ProviderBeaconBeacon.finish_registration.closure.Insts.CoreOpsFunctionFnOnceTuplekexresponseOptionResponsePacket parsed ()

attribute [local irreducible] beaconcrypt_parse.extraction_decode_response

theorem response_packet (input : Slice U8) :
    (responsePacket (m := m) input).run =
      pure (@RegistrationNativePacketReadback.decodeResponse RegistrationNativeConcreteCodec.decoderOperations input) := by
  unfold responsePacket RegistrationNativePacketReadback.decodeResponse
  change (do
    let parsed ← (liftRust (@beaconcrypt_parse.extraction_decode_response RegistrationNativeConcreteCodec.decoderOperations input) : RustT m _)
    AdapterPublicWrapperRequestMonad.Option.and_then
      beaconcrypt_public_request.beacon.ProviderBeaconBeacon.finish_registration.closure.Insts.CoreOpsFunctionFnOnceTuplekexresponseOptionResponsePacket parsed ()).run = _
  simp only [RustT.run_bind, RustT.run_liftRust, pure_bind]
  cases parsedRun : @beaconcrypt_parse.extraction_decode_response RegistrationNativeConcreteCodec.decoderOperations input with
  | fail error | div => rfl
  | ok optional => cases optional with
    | none => rfl
    | some value => rfl

def initPacket (input : Slice U8) : RustT m (Option registration.InitPacket) := do
  let parsed ← @Codecs.decodeInit (RustT m) (codecs (m := m)) input
  match parsed with
  | .none => pure .none
  | .some value => liftRust (registration.InitPacket.from_slices value.identity_key value.pre_key
      value.one_time_key value.pq_key)

attribute [local irreducible] beaconcrypt_parse.extraction_decode_init

theorem init_packet (input : Slice U8) :
    (initPacket (m := m) input).run =
      pure (@RegistrationNativePacketReadback.decodeInit RegistrationNativeConcreteCodec.decoderOperations input) := by
  unfold initPacket RegistrationNativePacketReadback.decodeInit
  change (do
    let parsed ← (liftRust (@beaconcrypt_parse.extraction_decode_init RegistrationNativeConcreteCodec.decoderOperations input) : RustT m _)
    match parsed with
    | .none => (pure .none : RustT m (Option registration.InitPacket))
    | .some value => liftRust (registration.InitPacket.from_slices value.identity_key value.pre_key
        value.one_time_key value.pq_key)).run = _
  simp only [RustT.run_bind, RustT.run_liftRust, pure_bind]
  cases parsedRun : @beaconcrypt_parse.extraction_decode_init RegistrationNativeConcreteCodec.decoderOperations input with
  | fail error | div => rfl
  | ok optional => cases optional <;> rfl

omit [Monad m] [LawfulMonad m] in
theorem input_roundtrip (input : Slice U8) :
    FrameCodecReadBack.inputSlice (TranscriptAuthParts.absSlice input)
      (by simpa only [TranscriptAuthParts.absSlice, List.length_map, UScalar.max_USize_eq] using input.property) = input := by
  apply Subtype.ext
  simp only [FrameCodecReadBack.inputSlice, TranscriptAuthParts.absSlice, List.map_map]
  change List.map (fun byte => ProtocolComposition.concreteByte (PqxdhRefinement.absByte byte)) input.val = input.val
  simp only [FrameCodecReadBack.concrete_abs_byte]
  change List.map id input.val = input.val
  exact List.map_id input.val

theorem response_source (input : Slice U8) :
    (responsePacket (m := m) input).run =
      pure (.ok (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input))) := by
  have bound : (TranscriptAuthParts.absSlice input).length ≤ UScalar.max .Usize := by
    simpa only [TranscriptAuthParts.absSlice, List.length_map, UScalar.max_USize_eq] using input.property
  obtain ⟨reply, normal, decoded⟩ := RegistrationNativeConcreteCodec.response_normal (TranscriptAuthParts.absSlice input) bound
  rw [input_roundtrip] at normal
  rw [response_packet, normal, decoded]

theorem init_source (input : Slice U8) :
    (initPacket (m := m) input).run =
      pure (.ok (RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input))) := by
  have bound : (TranscriptAuthParts.absSlice input).length ≤ UScalar.max .Usize := by
    simpa only [TranscriptAuthParts.absSlice, List.length_map, UScalar.max_USize_eq] using input.property
  obtain ⟨reply, normal, decoded⟩ := RegistrationNativeConcreteCodec.init_normal (TranscriptAuthParts.absSlice input) bound
  rw [input_roundtrip] at normal
  rw [init_packet, normal, decoded]
end BeaconcryptCore.Refinement.AdapterPublicConcreteCodecs
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicConcreteCodecs.response_packet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicConcreteCodecs.response_packet

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicConcreteCodecs.init_packet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicConcreteCodecs.init_packet

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicConcreteCodecs.input_roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicConcreteCodecs.input_roundtrip

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicConcreteCodecs.response_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicConcreteCodecs.response_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicConcreteCodecs.init_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicConcreteCodecs.init_source

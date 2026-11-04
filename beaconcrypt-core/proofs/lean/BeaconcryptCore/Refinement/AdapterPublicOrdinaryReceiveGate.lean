-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicOrdinaryEnvelope
import BeaconcryptCore.Refinement.AdapterPublicConcreteCodecs
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperiment
/-! Exact ordinary SDK frame parsing and sender admission on the original source slice. Payload admission remains at begin_record_receive, at its actual later source stage. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace BeaconcryptCore.Refinement.AdapterPublicOrdinaryReceiveGate
open BeaconcryptCore.Computational

private theorem empty (bytes : Slice U8) :
    core.slice.Slice.is_empty bytes=.ok bytes.val.isEmpty := by
  change RustM.ok (decide (bytes.len=0#usize))=_
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,List.isEmpty_iff_length_eq_zero]
  constructor
  · intro zero
    have length := congrArg UScalar.val zero
    simpa [Slice.len_val,Slice.length] using length
  · intro zero
    apply UScalar.eq_of_val_eq
    simpa [Slice.len_val,Slice.length] using zero

def admitted (expected : U64) (frame : CborProductionBoundary.NativeFrame) : Option transport.FrameView :=
  if frame.sender=expected then some ⟨frame.sequence,frame.sender,frame.payload⟩ else none

theorem decode (bytes : Slice U8) :
    ∃parsed,beaconcrypt_public_ordinary.ratchet.decode_crypto_frame bytes=.ok parsed ∧
      RegistrationNativeConcreteCodec.wire.parseFrame (TranscriptAuthParts.absSlice bytes)=
        (fun frame =>(⟨frame.seq,frame.key_id,frame.cipher_text⟩ : CborProductionBoundary.NativeFrame)) <$>parsed := by
  have bound : (TranscriptAuthParts.absSlice bytes).length≤UScalar.max .Usize := by
    simpa only [TranscriptAuthParts.absSlice,List.length_map,UScalar.max_USize_eq] using bytes.property
  obtain ⟨parsed,normal,projected⟩ := RegistrationNativeConcreteCodec.frame_normal (TranscriptAuthParts.absSlice bytes) bound
  rw [AdapterPublicConcreteCodecs.input_roundtrip] at normal
  exact ⟨parsed,normal,projected⟩

theorem prepare (bytes : Slice U8) (expected : U64) :
    AdapterPublicOrdinaryEnvelope.prepareReceive bytes expected=.ok
      ((RegistrationNativeConcreteCodec.wire.parseFrame (TranscriptAuthParts.absSlice bytes)).bind (admitted expected)) := by
  obtain ⟨parsed,normal,projected⟩ := decode bytes
  have rawNormal : beaconcrypt_parse.frame.decode bytes=.ok parsed := normal
  by_cases emptyInput : bytes.val.isEmpty=true
  · have length : bytes.val.length=0 := List.isEmpty_iff_length_eq_zero.mp emptyInput
    have rejected:=FrameCodecRoundtrip.decode_short bytes (by omega)
    have absent : parsed=none := RustM.ok.inj (rawNormal.symm.trans rejected)
    rw [absent] at normal projected
    simp [AdapterPublicOrdinaryEnvelope.prepareReceive,empty,emptyInput,projected]
  · have nonempty : bytes.val.isEmpty=false := Bool.eq_false_iff.mpr emptyInput
    cases parsed with
    | none =>
        simp [AdapterPublicOrdinaryEnvelope.prepareReceive,empty,nonempty,normal,projected,
          core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
          core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]
    | some frame =>
        by_cases same : frame.key_id=expected
        · subst expected
          simp [AdapterPublicOrdinaryEnvelope.prepareReceive,empty,nonempty,normal,projected,
            core.option.Option.Insts.CoreOpsTry_traitTry.branch,
            core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
            core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
            transport.admit_frame,admitted]
        · have valueDifferent : frame.key_id.val≠expected.val := fun equal =>same (UScalar.eq_of_val_eq equal)
          simp [AdapterPublicOrdinaryEnvelope.prepareReceive,empty,nonempty,normal,projected,
            core.option.Option.Insts.CoreOpsTry_traitTry.branch,
            core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
            core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
            transport.admit_frame,admitted,same,valueDifferent]

theorem fields (bytes : Slice U8) (expected : U64) (view : transport.FrameView)
    (accepted : AdapterPublicOrdinaryEnvelope.prepareReceive bytes expected=.ok (some view)) :
    ∃frame,RegistrationNativeConcreteCodec.wire.parseFrame (TranscriptAuthParts.absSlice bytes)=some frame ∧
      frame.sequence=view.sequence ∧frame.sender=view.sender ∧frame.payload=view.ciphertext ∧view.sender=expected := by
  rw [prepare] at accepted
  have selected := RustM.ok.inj accepted
  obtain ⟨frame,parsed,admission⟩ := Option.bind_eq_some_iff.mp selected
  unfold admitted at admission
  split_ifs at admission with same
  · cases admission
    exact ⟨frame,parsed,rfl,rfl,rfl,same⟩

theorem frame_read (bytes : Slice U8) :
    (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire).frameRead (TranscriptAuthParts.absSlice bytes)=
      FrameCodecReadBack.nativeDecode (TranscriptAuthParts.absSlice bytes) := by
  change CborTransport.boundedDecoder (fun raw =>CborProductionBoundary.decoded <$>RegistrationNativeConcreteCodec.wire.parseFrame raw)
    (TranscriptAuthParts.absSlice bytes)=_
  simp_rw [RegistrationNativeConcreteCodec.frame_projection]
  change (if (TranscriptAuthParts.absSlice bytes).length≤33554432 then
    FrameCodecReadBack.nativeDecode (TranscriptAuthParts.absSlice bytes) else none)=_
  by_cases bounded : (TranscriptAuthParts.absSlice bytes).length≤33554432
  · rw [ite_eq_left bounded]
  · rw [ite_eq_right bounded,FrameCodecReadBack.nativeDecode_oversize _ (Nat.lt_of_not_ge bounded)]

theorem decoded_fields (bytes : Slice U8) (expected : U64) (view : transport.FrameView)
    (accepted : AdapterPublicOrdinaryEnvelope.prepareReceive bytes expected=.ok (some view)) :
    (RegistrationNativeWire.ledgerCodec RegistrationNativeConcreteCodec.wire).frameRead (TranscriptAuthParts.absSlice bytes)=
      some (⟨view.sequence,view.sender,TranscriptAuthParts.absSlice view.ciphertext⟩ : RawCtxReceive.DecodedFrame) := by
  obtain ⟨frame,parsed,sequence,sender,payload,_expected⟩ := fields bytes expected view accepted
  rw [frame_read,←RegistrationNativeConcreteCodec.frame_projection,parsed]
  change some (⟨frame.sequence,frame.sender,TranscriptAuthParts.absSlice frame.payload⟩ : RawCtxReceive.DecodedFrame)=_
  rw [sequence,sender,payload]

end BeaconcryptCore.Refinement.AdapterPublicOrdinaryReceiveGate
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryReceiveGate.decode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryReceiveGate.decode
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryReceiveGate.prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryReceiveGate.prepare
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryReceiveGate.fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryReceiveGate.fields

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryReceiveGate.frame_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryReceiveGate.frame_read
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicOrdinaryReceiveGate.decoded_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicOrdinaryReceiveGate.decoded_fields

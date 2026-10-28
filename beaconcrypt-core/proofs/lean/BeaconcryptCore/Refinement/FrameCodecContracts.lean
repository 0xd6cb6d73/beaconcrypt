-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.FrameCodecCanonical
import BeaconcryptCore.Refinement.FrameCodecReadBack
import BeaconcryptCore.Refinement.FrameCodecWriteBytes
import BeaconcryptCore.Computational.CborRegistrationCodec
import BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_parse PqxdhRefinement
open BeaconcryptCore.Computational
open BeaconcryptCore.Refinement.FrameCodecArgument
open BeaconcryptCore.Refinement.FrameCodecRoundtrip
open BeaconcryptCore.Refinement.FrameCodecRepresentation
open BeaconcryptCore.Refinement.FrameCodecReadBack
open BeaconcryptCore.Refinement.FrameCodecTotality

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.FrameCodecContracts

private theorem slice_index_exact (input : Slice U8) (index : Usize)
    (bound : index.val < input.val.length) :
    Slice.index_usize input index = ok input.val[index.val]! := by
  unfold Slice.index_usize
  rw [Slice.getElem?_Usize_eq, List.getElem?_eq_getElem bound,
    getElem!_pos input.val index.val bound]

private theorem header_list (bytes : List U8) (minimum : 3 ≤ bytes.length)
    (first : bytes[0]! = 133#u8) (second : bytes[1]! = 1#u8) (third : bytes[2]! = 2#u8) :
    bytes = [133#u8, 1#u8, 2#u8] ++ bytes.drop 3 := by
  cases bytes with
  | nil => simp at minimum
  | cons a tail =>
    cases tail with
    | nil => simp at minimum
    | cons b tail =>
      cases tail with
      | nil => simp at minimum
      | cons c tail =>
        simp only [List.getElem!_cons_zero] at first
        simp only [List.getElem!_cons_succ, List.getElem!_cons_zero] at second third
        subst a; subst b; subst c
        rfl

abbrev ArgumentCanonical := ∀ (input : Slice U8) (major : U8) (value : U64) (used : Usize),
  frame.decode_argument input major = ok (.Some (value, used)) →
  input.val.take used.val = argumentBytes major value ∧ used = (encoded major value).length

/-- Every complete accepted native frame consumes exactly its canonical bytes, including the whole payload. -/
theorem decode_canonical_of_arguments (canonical : ArgumentCanonical)
    (input : Slice U8) (parsed : frame.Frame)
    (decoded : frame.decode input = ok (.Some parsed)) :
    input.val = frameBytes parsed.seq parsed.key_id parsed.cipher_text ∧ input.val.length ≤ 33554432 := by
  by_cases large : 33554432 < input.val.length
  · rw [decode_oversize input large] at decoded
    cases decoded
  · by_cases short : input.val.length < 3
    · rw [decode_short input short] at decoded
      cases decoded
    · have minimum : 3 ≤ input.val.length := by omega
      have notLarge : ¬ input.len > (33554432#usize) := by
        simp only [UScalar.lt_equiv, Slice.len_val, Slice.length, UScalar.ofNatCore_val_eq]
        omega
      have notShort : ¬ input.len < (3#usize) := by
        simp only [UScalar.lt_equiv, Slice.len_val, Slice.length, UScalar.ofNatCore_val_eq]
        omega
      simp only [frame.decode, core.slice.Slice.len, rust_primitives.slice.slice_length,
        beaconcrypt_parse.beaconcrypt_core.transport.MAX_MESSAGE_SIZE,
        _root_.beaconcrypt_core.transport.MAX_MESSAGE_SIZE, bind_tc_ok,
        notLarge, notShort, ite_false] at decoded
      rw [slice_index_exact input 0#usize (by norm_num; omega)] at decoded
      simp only [bind_tc_ok] at decoded
      split at decoded
      · cases decoded
      · rename_i firstHeader
        have firstByte : input.val[0]! = 133#u8 := by apply UScalar.eq_of_val_eq; simpa using firstHeader
        rw [slice_index_exact input 1#usize (by norm_num; omega)] at decoded
        simp only [bind_tc_ok] at decoded
        split at decoded
        · cases decoded
        · rename_i secondHeader
          have secondByte : input.val[1]! = 1#u8 := by apply UScalar.eq_of_val_eq; simpa using secondHeader
          rw [slice_index_exact input 2#usize (by norm_num; omega)] at decoded
          simp only [bind_tc_ok] at decoded
          split at decoded
          · cases decoded
          · rename_i thirdHeader
            have thirdByte : input.val[2]! = 2#u8 := by apply UScalar.eq_of_val_eq; simpa using thirdHeader
            rw [suffix_exact input 3#usize (by norm_num; omega)] at decoded
            simp only [bind_tc_ok, show (3#usize).val = 3 from rfl] at decoded
            obtain ⟨first, firstRead, firstBound⟩ := decode_argument_total (suffix input 3) 0#u8
            rw [firstRead] at decoded
            cases first with
            | none =>
                simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                  core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
                  core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
                  bind_tc_ok] at decoded
                cases decoded
            | some first =>
                rcases first with ⟨sequence, usedFirst⟩
                simp! only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                  core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, bind_tc_ok] at decoded
                rw [suffix_exact (suffix input 3) usedFirst firstBound.2] at decoded
                simp only [bind_tc_ok] at decoded
                obtain ⟨second, secondRead, secondBound⟩ :=
                  decode_argument_total (suffix (suffix input 3) usedFirst.val) 0#u8
                rw [secondRead] at decoded
                cases second with
                | none =>
                    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
                      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
                      bind_tc_ok] at decoded
                    cases decoded
                | some second =>
                    rcases second with ⟨sender, usedSecond⟩
                    simp! only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, bind_tc_ok] at decoded
                    rw [suffix_exact _ usedSecond secondBound.2] at decoded
                    simp only [bind_tc_ok] at decoded
                    obtain ⟨third, thirdRead, thirdBound⟩ :=
                      decode_argument_total (suffix (suffix (suffix input 3) usedFirst.val) usedSecond.val) 2#u8
                    rw [thirdRead] at decoded
                    cases third with
                    | none =>
                        simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                          core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
                          core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
                          bind_tc_ok] at decoded
                        cases decoded
                    | some third =>
                        rcases third with ⟨length, usedThird⟩
                        simp! only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
                          core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, bind_tc_ok] at decoded
                        rw [suffix_exact _ usedThird thirdBound.2] at decoded
                        simp only [bind_tc_ok, lift] at decoded
                        split at decoded
                        · cases decoded
                        · rename_i lengthHeader
                          have parsedSame := _root_.Option.some.inj (RustM.ok.inj decoded)
                          cases parsedSame
                          have firstPrefix := (canonical _ _ _ _ firstRead).1
                          have secondPrefix := (canonical _ _ _ _ secondRead).1
                          have thirdPrefix := (canonical _ _ _ _ thirdRead).1
                          have firstView := List.take_append_drop usedFirst.val (suffix input 3).val
                          rw [firstPrefix] at firstView
                          have secondView := List.take_append_drop usedSecond.val (suffix (suffix input 3) usedFirst.val).val
                          rw [secondPrefix] at secondView
                          have thirdView := List.take_append_drop usedThird.val (suffix (suffix (suffix input 3) usedFirst.val) usedSecond.val).val
                          rw [thirdPrefix] at thirdView
                          have headerView := header_list input.val minimum firstByte secondByte thirdByte
                          have lengthSame : length = UScalar.cast .U64
                              (suffix (suffix (suffix (suffix input 3) usedFirst.val) usedSecond.val) usedThird.val).len := by
                            apply UScalar.eq_of_val_eq
                            simpa using lengthHeader
                          refine ⟨?_, by omega⟩
                          have restThird := thirdView.symm
                          have restSecond := secondView.symm.trans
                            (congrArg (fun rest => argumentBytes 0#u8 sender ++ rest) restThird)
                          have restFirst := firstView.symm.trans
                            (congrArg (fun rest => argumentBytes 0#u8 sequence ++ rest) restSecond)
                          have whole := headerView.trans
                            (congrArg (fun rest => [133#u8, 1#u8, 2#u8] ++ rest) restFirst)
                          simpa only [frameBytes, lengthSame, List.append_assoc, suffix] using whole

/-- Accepted facade replies inherit exact native bytes and the complete-message bound. -/
theorem nativeDecode_canonical_of_arguments (canonical : ArgumentCanonical)
    (bytes : Pqxdh.Bytes) (parsed : RawCtxReceive.DecodedFrame)
    (decoded : nativeDecode bytes = some parsed) :
    CborTransport.render parsed = bytes ∧ bytes.length ≤ 33554432 ∧ parsed.payload.length < 2 ^ 64 := by
  by_cases inside : bytes.length ≤ 33554432
  · let input := inputSlice bytes (inside.trans Transport.message_limit_representable)
    obtain ⟨reply, normal⟩ := FrameCodecDecodeTotality.decode_total input
    cases reply with
    | none =>
        simp only [nativeDecode, dite_eq_left inside] at decoded
        change (match frame.decode input with | ok (.Some parsed) => _ | _ => none) = _ at decoded
        rw [normal] at decoded
        cases decoded
    | some native =>
        simp only [nativeDecode, dite_eq_left inside] at decoded
        change (match frame.decode input with | ok (.Some parsed) => _ | _ => none) = _ at decoded
        rw [normal] at decoded
        have same := _root_.Option.some.inj decoded
        cases same
        obtain ⟨nativeView, _⟩ := decode_canonical_of_arguments canonical input native normal
        have inputView : input.val.map absByte = bytes := by
          change (bytes.map ProtocolComposition.concreteByte).map absByte = bytes
          simp [List.map_map, Function.comp_def, ProtocolComposition.absByte_concreteByte]
        have abstractView := congrArg (List.map absByte) nativeView
        rw [inputView, frame_abs] at abstractView
        refine ⟨abstractView.symm, inside, ?_⟩
        have bound := (UScalar.cast .U64 native.cipher_text.len).bv.isLt
        change (UScalar.cast .U64 native.cipher_text.len).val < 2 ^ 64 at bound
        rw [Transport.usize_to_u64_value, Slice.len_val] at bound
        simpa only [List.length_map, Slice.length] using bound
  · rw [nativeDecode, dite_eq_right inside] at decoded
    cases decoded

/-- The logical writer has the actual canonical writer's complete-message admission domain. -/
noncomputable def nativeWrite (frame : RawCtxReceive.DecodedFrame) : Option Pqxdh.Bytes :=
  if frame.payload.length < 2 ^ 64 ∧ (CborTransport.render frame).length ≤ 33554432
  then some (CborTransport.render frame) else none

/-- Replace only established-frame readers and writers by the concrete codec proved here. -/
noncomputable def withFrames {Reader Response : Type}
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) : PqxdhServerAuthExperiment.Codec Reader Response :=
  { codec with frameRead := nativeDecode, frameWrite := nativeWrite }

/-- Every successful logical write is nonempty and reads back through the actual extracted parser. -/
theorem frame_readBack {Reader Response : Type}
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) :
    PqxdhServerAuthNegativeControl.FrameReadBack (withFrames codec) := by
  intro frame bytes written
  change nativeWrite frame = some bytes at written
  unfold nativeWrite at written
  split at written
  · rename_i domain
    have same := _root_.Option.some.inj written
    subst bytes
    refine ⟨?_, render_readback frame domain.1 domain.2⟩
    simp only [CborTransport.render, ite_eq_left domain.1]
    simp
  · cases written

/-- Canonical accepted bytes discharge the registration codec's stability obligation. -/
theorem stable_of_arguments (canonical : ArgumentCanonical) {Reader Response : Type}
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) :
    CborRegistrationCodec.Stable (withFrames codec) := by
  intro bytes frame decoded
  exact (nativeDecode_canonical_of_arguments canonical bytes frame decoded).1

/-- Every actually accepted frame lies in the concrete writer's admitted domain. -/
theorem readWritable_of_arguments (canonical : ArgumentCanonical) :
    PqxdhFirstBeaconRecordCanonical.ReadWritable nativeWrite nativeDecode := by
  intro bytes frame decoded
  obtain ⟨canonicalView, fits, representable⟩ := nativeDecode_canonical_of_arguments canonical bytes frame decoded
  refine ⟨CborTransport.render frame, ?_⟩
  unfold nativeWrite
  rw [ite_eq_left ⟨representable, by simpa only [canonicalView] using fits⟩]

def emptySlice : Slice U8 := ⟨[], by simp⟩

/-- Every logical write is witnessed by normal execution of the actual extracted writer into a sufficient concrete destination; allocation itself remains external. -/
theorem nativeWrite_source (frame : RawCtxReceive.DecodedFrame) (bytes : Pqxdh.Bytes)
    (written : nativeWrite frame = some bytes) :
    ∃ (payload output : Slice U8) (length : Usize) (result : Slice U8),
      payload.val.map absByte = frame.payload ∧ output.val.length = bytes.length ∧
      beaconcrypt_parse.frame.encode_three frame.sequence frame.sender payload emptySlice emptySlice output = ok (length, result) ∧
      length.val = bytes.length ∧ (result.val.take length.val).map absByte = bytes := by
  unfold nativeWrite at written
  split at written
  · rename_i domain
    have same := _root_.Option.some.inj written
    subst bytes
    let payload := inputSlice frame.payload
      (((payload_le_render frame domain.1).trans domain.2).trans Transport.message_limit_representable)
    have payloadView : payload.val.map absByte = frame.payload := by
      change (frame.payload.map ProtocolComposition.concreteByte).map absByte = frame.payload
      simp [List.map_map, Function.comp_def, ProtocolComposition.absByte_concreteByte]
    let output : Slice U8 := ⟨List.replicate (CborTransport.render frame).length 0#u8,
      by simpa only [List.length_replicate, UScalar.max_USize_eq] using
        domain.2.trans Transport.message_limit_representable⟩
    have frameView : (⟨frame.sequence, frame.sender, payload.val.map absByte⟩ : RawCtxReceive.DecodedFrame) = frame := by
      cases frame
      simp only [payloadView]
    have wireLength : (frameBytes frame.sequence frame.sender payload).length =
        (CborTransport.render frame).length := by
      simpa only [List.length_map, frameView] using
        congrArg List.length (frame_abs frame.sequence frame.sender payload)
    obtain ⟨length, result, run, size, bytes⟩ := FrameCodecWriteBytes.encode_three_render
      frame.sequence frame.sender payload emptySlice emptySlice payload output
      (by simp [emptySlice]) (by omega)
      (by simp only [output, List.length_replicate]; omega)
    refine ⟨payload, output, length, result, payloadView, ?_, run, ?_, ?_⟩
    · simp only [output, List.length_replicate]
    · simpa only [frameView] using size
    · simpa only [frameView] using bytes
  · cases written

/-- Actual accepted native frames are canonical; the scalar accepted-prefix property is fully discharged. -/
theorem decode_canonical (input : Slice U8) (parsed : frame.Frame)
    (decoded : frame.decode input = ok (.Some parsed)) :
    input.val = frameBytes parsed.seq parsed.key_id parsed.cipher_text ∧ input.val.length ≤ 33554432 :=
  decode_canonical_of_arguments FrameCodecCanonical.decode_argument_canonical input parsed decoded

/-- Every actual accepted byte string is the canonical rendering of its parsed frame. -/
theorem nativeDecode_canonical (bytes : Pqxdh.Bytes) (parsed : RawCtxReceive.DecodedFrame)
    (decoded : nativeDecode bytes = some parsed) :
    CborTransport.render parsed = bytes ∧ bytes.length ≤ 33554432 ∧ parsed.payload.length < 2 ^ 64 :=
  nativeDecode_canonical_of_arguments FrameCodecCanonical.decode_argument_canonical bytes parsed decoded

/-- Concrete native frame parsing discharges the existing registration stability contract. -/
theorem stable {Reader Response : Type} (codec : PqxdhServerAuthExperiment.Codec Reader Response) :
    CborRegistrationCodec.Stable (withFrames codec) :=
  stable_of_arguments FrameCodecCanonical.decode_argument_canonical codec

/-- Concrete native frame parsing and the source-backed bounded writer discharge readable-frame writability. -/
theorem readWritable {Reader Response : Type} (codec : PqxdhServerAuthExperiment.Codec Reader Response) :
    PqxdhFirstBeaconRecordCanonical.ReadWritable (withFrames codec).frameWrite (withFrames codec).frameRead :=
  readWritable_of_arguments FrameCodecCanonical.decode_argument_canonical

/-- All three existing frame codec obligations hold for the concrete adapter, with no assumed parser or writer law. -/
theorem contracts {Reader Response : Type} (codec : PqxdhServerAuthExperiment.Codec Reader Response) :
    PqxdhServerAuthNegativeControl.FrameReadBack (withFrames codec) ∧
      CborRegistrationCodec.Stable (withFrames codec) ∧
      PqxdhFirstBeaconRecordCanonical.ReadWritable (withFrames codec).frameWrite (withFrames codec).frameRead :=
  ⟨frame_readBack codec, stable codec, readWritable codec⟩

end BeaconcryptCore.Refinement.FrameCodecContracts

/-- info: 'BeaconcryptCore.Refinement.FrameCodecContracts.decode_canonical_of_arguments' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecContracts.decode_canonical_of_arguments

/-- info: 'BeaconcryptCore.Refinement.FrameCodecContracts.nativeDecode_canonical_of_arguments' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecContracts.nativeDecode_canonical_of_arguments

/-- info: 'BeaconcryptCore.Refinement.FrameCodecContracts.frame_readBack' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecContracts.frame_readBack

/-- info: 'BeaconcryptCore.Refinement.FrameCodecContracts.stable_of_arguments' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecContracts.stable_of_arguments

/-- info: 'BeaconcryptCore.Refinement.FrameCodecContracts.readWritable_of_arguments' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecContracts.readWritable_of_arguments

/-- info: 'BeaconcryptCore.Refinement.FrameCodecContracts.nativeWrite_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecContracts.nativeWrite_source

/-- info: 'BeaconcryptCore.Refinement.FrameCodecContracts.decode_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecContracts.decode_canonical

/-- info: 'BeaconcryptCore.Refinement.FrameCodecContracts.nativeDecode_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecContracts.nativeDecode_canonical

/-- info: 'BeaconcryptCore.Refinement.FrameCodecContracts.stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecContracts.stable

/-- info: 'BeaconcryptCore.Refinement.FrameCodecContracts.readWritable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecContracts.readWritable

/-- info: 'BeaconcryptCore.Refinement.FrameCodecContracts.contracts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecContracts.contracts

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.FrameCodecExtraction.Funs

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_parse

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.FrameCodecWriter

/-- A rejected payload length leaves the output untouched. -/
theorem header_rejected (sequence sender : U64) (payloadLength : Usize) (output : Slice U8)
    (rejected : _root_.beaconcrypt_core.transport.encoded_frame_len sequence sender payloadLength = ok .None) :
    frame.write_header sequence sender payloadLength output = ok (.None, output) := by
  simp only [frame.write_header, rejected, bind_tc_ok,
    CoreModels.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    CoreModels.core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    CoreModels.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]

/-- The native writer checks capacity before touching the destination. -/
theorem header_short_output (sequence sender : U64) (payloadLength length : Usize) (output : Slice U8)
    (admitted : _root_.beaconcrypt_core.transport.encoded_frame_len sequence sender payloadLength = ok (.Some length))
    (short : output.len < length) :
    frame.write_header sequence sender payloadLength output = ok (.None, output) := by
  simp only [frame.write_header, admitted, bind_tc_ok,
    CoreModels.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    CoreModels.core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
    CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length, short, ite_true]

/-- An overflow while adding the first two chunks returns failure without mutation. -/
theorem first_length_overflow (sequence sender : U64) (first second third output : Slice U8)
    (overflow : CoreModels.core.num.Usize.checked_add first.len second.len = ok .None) :
    frame.encode_three sequence sender first second third output = ok (0#usize, output) := by
  simp only [frame.encode_three, CoreModels.core.slice.Slice.len,
    CoreModels.rust_primitives.slice.slice_length, bind_tc_ok, overflow]

/-- An overflow while adding the final chunk also returns failure without mutation. -/
theorem complete_length_overflow (sequence sender : U64) (first second third output : Slice U8)
    (prefixLength : Usize)
    (prefixSum : CoreModels.core.num.Usize.checked_add first.len second.len = ok (.Some prefixLength))
    (overflow : CoreModels.core.num.Usize.checked_add prefixLength third.len = ok .None) :
    frame.encode_three sequence sender first second third output = ok (0#usize, output) := by
  simp only [frame.encode_three, CoreModels.core.slice.Slice.len,
    CoreModels.rust_primitives.slice.slice_length, bind_tc_ok, prefixSum, overflow]

end BeaconcryptCore.Refinement.FrameCodecWriter

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriter.header_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriter.header_rejected

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriter.header_short_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriter.header_short_output

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriter.first_length_overflow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriter.first_length_overflow

/-- info: 'BeaconcryptCore.Refinement.FrameCodecWriter.complete_length_overflow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.FrameCodecWriter.complete_length_overflow

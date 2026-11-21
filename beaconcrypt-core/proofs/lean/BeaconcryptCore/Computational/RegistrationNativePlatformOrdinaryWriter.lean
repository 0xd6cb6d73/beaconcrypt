-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterRecordFrameBytes
import BeaconcryptCore.Computational.RegistrationNativeExtractedAllocation

/-! Ongoing frame writing interprets the actual source codec as trusted pure serialization. The only external leaf receives the public capacity and can update its common platform state on either reservation outcome. It receives no chunks, plaintext, key, unpublished packet or private map. Successful writer readback is a consequence of the actual Frame3 source program. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWriter
open BeaconcryptCore.Refinement
open PqxdhRefinement
variable {E : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

def capacity (frame : RawCtxReceive.DecodedFrame) : Option Nat :=
  let size := CborSizing.frameLen frame.sequence.val frame.sender.val frame.payload.length
  if size ≤ 33554432 then some size else none

def write (reserve : Nat → m (core.result.Result Unit E)) (frame : RawCtxReceive.DecodedFrame) : m (Option Pqxdh.Bytes) :=
  match capacity frame with
  | none => pure none
  | some size => do
      let reserved ← reserve size
      match reserved with
      | .Err _ => pure none
      | .Ok _ => pure (some (CborTransport.render frame))

/-- The complete actual source Frame3 helper has exactly this dynamic normal-return interpretation; the allocator sees only its real empty-buffer reservation capacity. -/
theorem source [FrameDispatchFallback.Operations]
    (reserve : Nat → m (core.result.Result Unit E)) (sequence sender : U64)
    (first second third payload : Slice U8) (prefixLength sourceCapacity : Usize)
    (prefixSum : first.val.length + second.val.length = prefixLength.val)
    (payloadView : payload.val = first.val ++ second.val ++ third.val)
    (admitted : beaconcrypt_core.transport.encoded_frame_len sequence sender payload.len = .ok (.Some sourceCapacity)) :
    RegistrationNativeExtractedAllocation.abstractResult <$>
      AdapterRecordFrameBytes.frame (fun _ size => .ok <$> reserve size.val)
        (AdapterRecordFrameBytes.serializer (m := m)) sequence sender first second third =
      .ok <$> write reserve ⟨sequence, sender, TranscriptAuthParts.absSlice payload⟩ := by
  obtain ⟨sourceSize, bounded⟩ := AdapterRecordFrameBytes.capacity_value sequence sender payload sourceCapacity admitted
  have exactSize : sourceCapacity.val = CborSizing.frameLen sequence.val sender.val payload.val.length := by
    rw [sourceSize]
    have frameView : FrameCodecRepresentation.frameBytes sequence sender payload = FrameCodecWriteBytes.headerBytes sequence sender payload.len ++ payload.val := rfl
    rw [frameView, List.length_append]
    simpa only [Slice.len_val, Slice.length] using FrameCodecWriteBytes.header_size sequence sender payload.len
  have permitted : CborSizing.frameLen sequence.val sender.val payload.val.length ≤ 33554432 := by
    rw [← exactSize, sourceSize]
    exact bounded
  rw [AdapterRecordFrameBytes.frame_bytes _ sequence sender first second third payload prefixLength sourceCapacity prefixSum payloadView admitted]
  simp only [write, capacity, TranscriptAuthParts.absSlice, List.length_map, permitted, ite_true, map_bind]
  rw [← exactSize]
  rw [← bind_pure_comp, ← bind_pure_comp]
  simp only [bind_assoc, bind_map_left, pure_bind]
  apply bind_congr
  intro reserved
  cases reserved with
  | Err error =>
      simp only [bind_tc_ok, RegistrationNativeExtractedAllocation.abstractResult,
        RegistrationNativeExtractedAllocation.output, Option.map_none, map_pure]
  | Ok success =>
      simp only [bind_tc_ok, RegistrationNativeExtractedAllocation.abstractResult,
        RegistrationNativeExtractedAllocation.output, RegistrationNativeExtractedAllocation.bytes,
        Option.map_some, map_pure]
      rw [FrameCodecRepresentation.frame_abs]

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWriter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWriter.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWriter.source

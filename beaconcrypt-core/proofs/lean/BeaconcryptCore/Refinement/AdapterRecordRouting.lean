-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterRecordRoutingExtraction.Funs

/-! The actual production record write dispatcher receives a fixed three-part core value. Its Frame branch forwards exactly those three slices to the runtime frame writer; its Raw branch forwards the same array to the raw join helper. Neither branch changes metadata or invents another chunk. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.AdapterRecordRouting
open beaconcrypt_record_routing
variable [callbacks : RecordRoutingCallbacks.Operations]

theorem raw (parts : Array (Slice U8) 3#usize) :
    ratchet.execute_write_request (.Raw parts) = callbacks.join parts := rfl

theorem frame (parts : Array (Slice U8) 3#usize) (sequence sender : U64) :
    ratchet.execute_write_request (.Frame parts sequence sender) =
      callbacks.frame sequence sender (Array.to_slice parts) := rfl

omit callbacks in
theorem frame_parts_length (parts : Array (Slice U8) 3#usize) :
    (Array.to_slice parts).val.length = 3 := parts.property

theorem frame_selected (parts : Array (Slice U8) 3#usize) (sequence sender : U64) :
    ratchet.execute_write_request (.Frame parts sequence sender) =
      callbacks.frame sequence sender (Array.to_slice parts) ∧
    (Array.to_slice parts).val = parts.val ∧ (Array.to_slice parts).val.length = 3 :=
  ⟨frame parts sequence sender, rfl, frame_parts_length parts⟩

end BeaconcryptCore.Refinement.AdapterRecordRouting

/-- info: 'BeaconcryptCore.Refinement.AdapterRecordRouting.raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordRouting.raw
/-- info: 'BeaconcryptCore.Refinement.AdapterRecordRouting.frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordRouting.frame
/-- info: 'BeaconcryptCore.Refinement.AdapterRecordRouting.frame_parts_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordRouting.frame_parts_length
/-- info: 'BeaconcryptCore.Refinement.AdapterRecordRouting.frame_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterRecordRouting.frame_selected

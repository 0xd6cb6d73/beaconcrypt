-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterRecordHelperRouting
import BeaconcryptCore.PanicFreedom.AdapterRecordHelpers

/-! Safety of the production record dispatcher. Only its actual three-chunk routes require normal callbacks; generic callbacks at other shapes remain unrestricted. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.PanicFreedom.AdapterRecordRouting
variable [operations : Refinement.RecordRoutingCallbacks.Operations]

structure Contracts : Prop where
  join : ∀ (parts : Std.Array (Slice U8) 3#usize), ∃ result, operations.join parts = ok result
  frame : ∀ sequence sender (parts : Std.Array (Slice U8) 3#usize),
    ∃ result, operations.frame sequence sender (Std.Array.to_slice parts) = ok result

theorem execute_write_request_total (contracts : Contracts) (request : record_effects.RecordWriteRequest) :
    ∃ result, beaconcrypt_record_routing.ratchet.execute_write_request request = ok result := by
  cases request with
  | Raw parts => exact contracts.join parts
  | Frame parts sequence sender =>
    simpa only [beaconcrypt_record_routing.ratchet.execute_write_request, lift, bind_tc_ok,
      beaconcrypt_record_routing.wire.encode_frame_parts] using contracts.frame sequence sender parts

/- Instantiating the production route by the separately source-checked specialized helpers discharges both callback contracts at every reached shape. -/
omit operations in
theorem source_callbacks_total [Refinement.AdapterWirePrimitive.Operations]
    [Refinement.FrameDispatchFallback.Operations] (allocation : AdapterWire.Contracts)
    (other : Refinement.RecordRoutingCallbacks.Operations) (request : record_effects.RecordWriteRequest) :
    ∃ result, @beaconcrypt_record_routing.ratchet.execute_write_request
      (Refinement.AdapterRecordHelperRouting.sourceCallbacks other) request = ok result := by
  cases request with
  | Raw parts =>
    simpa only [Refinement.AdapterRecordHelperRouting.source_raw] using
      AdapterRecordHelpers.join_total allocation parts
  | Frame parts sequence sender =>
    simpa only [Refinement.AdapterRecordHelperRouting.source_frame] using
      AdapterRecordHelpers.encode_frame_total allocation sequence sender parts

end BeaconcryptCore.PanicFreedom.AdapterRecordRouting

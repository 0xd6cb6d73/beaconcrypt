-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Extraction.Funs
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.RecordRoutingCallbacks
/-! The actual source route is independent of the helper implementations. The raw join and generic frame writer remain explicit callbacks pending their separate source instantiations. -/
class Operations where
  join {N : Usize} : Array (Slice U8) N → RustM (core.option.Option (alloc.vec.Vec U8))
  frame : U64 → U64 → Slice (Slice U8) → RustM (core.option.Option (alloc.vec.Vec U8))
end BeaconcryptCore.Refinement.RecordRoutingCallbacks
namespace beaconcrypt_record_routing
variable [ops : BeaconcryptCore.Refinement.RecordRoutingCallbacks.Operations]
def ratchet.join_record_parts {N : Usize} (parts : Array (Slice U8) N) := ops.join parts
def wire.encode_frame_parts := ops.frame
end beaconcrypt_record_routing

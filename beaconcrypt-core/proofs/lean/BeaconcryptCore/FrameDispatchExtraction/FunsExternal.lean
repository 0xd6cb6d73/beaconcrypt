-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.FrameCodecExtraction.Funs
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.FrameDispatchFallback
/-! Only the source path with more than three chunks remains abstract. The selected core writer always passes exactly three. -/
class Operations where
  many : U64 → U64 → Slice (Slice U8) → Slice U8 → RustM (Usize × Slice U8)
end BeaconcryptCore.Refinement.FrameDispatchFallback
namespace beaconcrypt_parse_dispatch.frame
abbrev encode_three := beaconcrypt_parse.frame.encode_three
def _proof_encode_many [ops : BeaconcryptCore.Refinement.FrameDispatchFallback.Operations] := ops.many
end beaconcrypt_parse_dispatch.frame

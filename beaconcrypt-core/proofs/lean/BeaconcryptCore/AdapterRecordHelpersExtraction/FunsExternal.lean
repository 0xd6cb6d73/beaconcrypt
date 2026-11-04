-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Extraction.Funs
import BeaconcryptCore.AdapterWireExtraction.Funs
import BeaconcryptCore.FrameDispatchExtraction.Funs
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true

namespace beaconcrypt_record_helpers.wire
abbrev encode_record := @beaconcrypt.wire.encode_record
end beaconcrypt_record_helpers.wire
namespace beaconcrypt_parse
variable [BeaconcryptCore.Refinement.FrameDispatchFallback.Operations]
abbrev encode_frame_parts := beaconcrypt_parse_dispatch.frame.encode_parts
end beaconcrypt_parse

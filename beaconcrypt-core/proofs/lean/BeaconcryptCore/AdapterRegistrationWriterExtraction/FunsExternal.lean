-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Extraction.Funs
import BeaconcryptCore.AdapterRegistrationWriterExtraction.Types
import BeaconcryptCore.AdapterWireExtraction.Funs
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true

namespace beaconcrypt_registration_writer.wire
abbrev encode_record := @beaconcrypt.wire.encode_record
end beaconcrypt_registration_writer.wire
namespace beaconcrypt_parse
variable [ops : BeaconcryptCore.Refinement.RegistrationWriterPrimitive.Operations]
def encode_init := ops.encodeInit
def encode_response := ops.encodeResponse
end beaconcrypt_parse

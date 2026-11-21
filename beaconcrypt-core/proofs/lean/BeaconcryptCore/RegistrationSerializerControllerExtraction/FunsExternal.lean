-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Extraction.Funs
import BeaconcryptCore.RegistrationSerializerControllerExtraction.Types
import BeaconcryptCore.RegistrationShallowExtraction.Funs
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace beaconcrypt_parse.registration_serializer_primitive
variable [ops : BeaconcryptCore.Refinement.RegistrationSerializerPrimitive.Operations]
def mkString := ops.mkString
def sizeRaw := ops.sizeRaw
def serializeRaw := ops.serializeRaw
def serializeArray := ops.serializeArray
def utf8Correct := ops.utf8Correct
end beaconcrypt_parse.registration_serializer_primitive

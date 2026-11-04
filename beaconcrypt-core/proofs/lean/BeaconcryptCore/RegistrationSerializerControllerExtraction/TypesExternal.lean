-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.RegistrationShallowExtraction.Types
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationSerializerPrimitive
/-! Explicit source codec calls. No functional law or security conclusion is a field.
All mutable slice poststates are returned. Concrete reachable source instances and
complete public codec laws are discharged separately. -/
class Operations where
  mkString : beaconcrypt_parse.cbordetver.cbor_det_string_kind → Slice U8 → RustM beaconcrypt_parse.cbordetver.bcExtractedToken6f7074696f6e5f5f43424f525f50756c73655f5261775f547970655f63626f725f726177
  sizeRaw : beaconcrypt_parse.cbordetveraux.cbor_raw → Slice Usize → RustM (Bool × Slice Usize)
  serializeRaw : beaconcrypt_parse.cbordetveraux.cbor_raw → Slice U8 → Usize → RustM (Usize × Slice U8)
  serializeArray : U64 → Slice U8 → Usize → RustM (Usize × Slice U8)
  utf8Correct : Slice U8 → RustM Bool
end BeaconcryptCore.Refinement.RegistrationSerializerPrimitive

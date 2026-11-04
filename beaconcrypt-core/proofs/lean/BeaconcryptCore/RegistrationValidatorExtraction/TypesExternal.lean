-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.RegistrationSchemaExtraction.Types
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.RegistrationValidatorPrimitive
/-! Complete effects for text and map-only branches. No parser law is a field. -/
class Operations where
  utf8Correct : Slice U8 → RustM Bool
  sortedMap : Slice U8 → Slice U8 → U64 → RustM Bool
end BeaconcryptCore.Refinement.RegistrationValidatorPrimitive

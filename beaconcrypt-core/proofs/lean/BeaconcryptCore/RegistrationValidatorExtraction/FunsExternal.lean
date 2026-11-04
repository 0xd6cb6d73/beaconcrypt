-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.RegistrationValidatorExtraction.Types
import BeaconcryptCore.RegistrationSchemaExtraction.Funs
import BeaconcryptCore.RegistrationHeaderOptimalExtraction.Funs
import BeaconcryptCore.RegistrationPreflightExtraction.Funs
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace beaconcrypt_parse.registration_validator_primitive
variable [ops : BeaconcryptCore.Refinement.RegistrationValidatorPrimitive.Operations]
def utf8Correct := ops.utf8Correct
def sortedMap := ops.sortedMap
def preflightSlice (input start fields : Slice U8) : RustM (core.option.Option Unit) := do
  let copied ← core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
    6#usize core.U8.Insts.CoreMarkerCopy fields
  match copied with
  | .Err _ => fail .panic
  | .Ok values => beaconcrypt_parse.preflight input start values
end beaconcrypt_parse.registration_validator_primitive

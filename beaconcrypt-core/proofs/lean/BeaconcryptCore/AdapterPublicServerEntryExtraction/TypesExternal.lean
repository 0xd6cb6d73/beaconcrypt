-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterPublicWrapperExtraction.Funs
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace beaconcrypt_public_server_entry
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Material]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Platform]
variable [BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]
abbrev server.Server := beaconcrypt_public_wrapper.server.Server
abbrev server.RegistrationOutput := beaconcrypt_public_wrapper.server.RegistrationOutput
end beaconcrypt_public_server_entry

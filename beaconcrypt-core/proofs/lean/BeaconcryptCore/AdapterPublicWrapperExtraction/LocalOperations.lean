-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterPublicWrapperExtraction.Types
import BeaconcryptCore.AdapterInitAuthenticationExtraction.Funs
import BeaconcryptCore.AdapterAuthenticationExtraction.Funs
import BeaconcryptCore.AdapterRecordExtraction.Funs
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.PublicWrapperPlatform
open beaconcrypt_public_wrapper
variable [Material] [Platform] [AdapterInitEdPrimitive.Operations]
class LocalOperations where
  auth_MldsaIdentity_public_key : auth.MldsaIdentity → RustM (Array Std.U8 1952#usize)
  auth_MldsaIdentity_sign_requested :
    auth.MldsaIdentity → beaconcrypt_core.registration.MldsaSigningRequest →
      RustM (core.option.Option (alloc.vec.Vec Std.U8))
  ratchet_initial_ratchet_hkdf :
    beaconcrypt_core.ratchet.InitialRatchetKdfRequest → RustM (Array Std.U8
      64#usize)
  collections_KeyedHasher_Insts_CoreHashBuildHasherSipHasher13_build_hasher : collections.KeyedHasher → RustM siphasher.sip.SipHasher13
  ratchet_execute_seal_request :
    beaconcrypt_core.record_effects.AeadSealRequest → RustM (core.option.Option
      ((alloc.vec.Vec Std.U8) × (Array Std.U8 16#usize)))
  ratchet_execute_write_request :
    beaconcrypt_core.record_effects.RecordWriteRequest → RustM
      (core.option.Option (alloc.vec.Vec Std.U8))
end BeaconcryptCore.Refinement.PublicWrapperPlatform

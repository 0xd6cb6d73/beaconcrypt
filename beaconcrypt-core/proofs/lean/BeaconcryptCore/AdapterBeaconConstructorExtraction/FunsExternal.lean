-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterBeaconConstructorExtraction.Types
import BeaconcryptCore.AdapterPublicWrapperExtraction.Funs
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.AdapterBeaconConstructorPrimitive
open PublicWrapperPlatform
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Material]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Platform]
variable [primitive : BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]

class Operations where
  mldsaGenerate {R E : Type} : rand_core.TryCryptoRng R E → R → RustM
    (core.result.Result beaconcrypt_public_wrapper.auth.MldsaIdentity Unit × R)
  edGenerate {R E : Type} : rand_core.TryCryptoRng R E → R → RustM
    (core.result.Result beaconcrypt_crypto.crypto_sign.KeyPair primitive.Error × R)
  kemGenerate {R E : Type} : rand_core.TryCryptoRng R E → R → RustM
    (core.result.Result beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair primitive.Error × R)
class Standard where
  OsError : Type
  os : rand_core.TryCryptoRng Unit OsError
  debug : core.fmt.Debug Unit
end BeaconcryptCore.Refinement.AdapterBeaconConstructorPrimitive
namespace beaconcrypt_constructor
open beaconcrypt_public_wrapper
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Material]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Platform]
variable [primitive : BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]

variable [ops : BeaconcryptCore.Refinement.AdapterBeaconConstructorPrimitive.Operations]
variable [beaconcrypt.auth.Operations]
def auth.MldsaIdentity.generate_with_rng {R E : Type} (rng : rand_core.TryCryptoRng R E) := ops.mldsaGenerate rng
def auth.fingerprint_pin := beaconcrypt_public_wrapper.auth.fingerprint_pin
variable [standard : BeaconcryptCore.Refinement.AdapterBeaconConstructorPrimitive.Standard]
def error.KeyGenError.Insts.CoreFmtDebug.fmt := standard.debug.fmt
end beaconcrypt_constructor
namespace beaconcrypt_crypto
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Material]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Platform]
variable [primitive : BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]

variable [ops : BeaconcryptCore.Refinement.AdapterBeaconConstructorPrimitive.Operations]
def crypto_sign.KeyPair.generate_with_rng {R E : Type} (rng : rand_core.TryCryptoRng R E) := ops.edGenerate rng
def crypto_kem.mlkem768.KeyPair.generate_with_rng {R E : Type} (rng : rand_core.TryCryptoRng R E) := ops.kemGenerate rng
variable [standard : BeaconcryptCore.Refinement.AdapterBeaconConstructorPrimitive.Standard]
def OsRng.Insts.Rand_coreTryCryptoRngError := standard.os
end beaconcrypt_crypto

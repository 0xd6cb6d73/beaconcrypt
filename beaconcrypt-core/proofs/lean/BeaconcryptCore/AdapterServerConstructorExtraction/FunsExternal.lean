-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterServerConstructorExtraction.Types
import BeaconcryptCore.AdapterBeaconConstructorExtraction.FunsExternal
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.AdapterServerConstructorPrimitive
variable [PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations]
/-- Individual std/storage and seeded-key leaves; constructor control flow is extracted. -/
class Standard where
  edFromSeed : Slice U8 → RustM (core.result.Result beaconcrypt_crypto.crypto_sign.KeyPair primitive.Error)
  mldsaFromSeed : Array U8 32#usize → RustM beaconcrypt_public_wrapper.auth.MldsaIdentity
  edSecretBytes : beaconcrypt_crypto.crypto_sign.SecretKey → RustM (Array U8 64#usize)
  mapWithKey (K V : Type) : Slice U8 → RustM (platform.Map K V platform.Hasher platform.Allocator)
  setWithKey (K : Type) : Slice U8 → RustM (platform.Set K platform.Hasher platform.Allocator)
  arcNew {T : Type} : T → RustM (platform.Arc T)
end BeaconcryptCore.Refinement.AdapterServerConstructorPrimitive
namespace beaconcrypt_server_constructor
open beaconcrypt_public_wrapper
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Material]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Platform]
variable [BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]
variable [ops : BeaconcryptCore.Refinement.AdapterBeaconConstructorPrimitive.Operations]
variable [standard : BeaconcryptCore.Refinement.AdapterServerConstructorPrimitive.Standard]
def auth.MldsaIdentity.generate_with_rng {R E : Type} (rng : rand_core.TryCryptoRng R E) := ops.mldsaGenerate rng
def auth.MldsaIdentity.from_seed := standard.mldsaFromSeed
def collections.map_with_key := standard.mapWithKey
def collections.set_with_key := standard.setWithKey
variable [sharedStandard : BeaconcryptCore.Refinement.AdapterBeaconConstructorPrimitive.Standard]
def error.KeyGenError.Insts.CoreFmtDebug.fmt := sharedStandard.debug.fmt
end beaconcrypt_server_constructor
namespace beaconcrypt_crypto
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Material]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Platform]
variable [BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]
variable [standard : BeaconcryptCore.Refinement.AdapterServerConstructorPrimitive.Standard]
def crypto_sign.KeyPair.from_seed := standard.edFromSeed
def crypto_sign.SecretKey.as_bytes := standard.edSecretBytes
end beaconcrypt_crypto
namespace CoreModels
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Material]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Platform]
variable [BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]
variable [standard : BeaconcryptCore.Refinement.AdapterServerConstructorPrimitive.Standard]
def alloc.sync.Arc.new {T : Type} := standard.arcNew (T := T)
end CoreModels

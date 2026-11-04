-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Extraction.Funs
import BeaconcryptCore.AdapterPublicWrapperExtraction.PlatformOperations

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true

/-! The original fixed-width ratchet KDF wrappers share the public adapter's existing HKDF extract operation and PRK representation. Only mutable expansion and the error formatter capability are added. The formatter has no execution-totality premise; successful Result.expect does not invoke it. Primitive security, native execution and physical erasure remain external boundaries. -/
namespace BeaconcryptCore.Refinement.AdapterRatchetKdfPrimitive
variable [PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]

class Operations where
  expandInto : Slice U8 → core.option.Option (Slice U8) →
    beaconcrypt_crypto.crypto_kdf.hkdf.sha512.Prk →
    RustM (core.result.Result Unit primitive.Error × Slice U8)
  errorDebug : core.fmt.Debug primitive.Error

end BeaconcryptCore.Refinement.AdapterRatchetKdfPrimitive

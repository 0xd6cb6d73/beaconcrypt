-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterInitAuthenticationExtraction.Types
import BeaconcryptCore.AdapterAuthenticationExtraction.FunsExternal
import BeaconcryptCore.Refinement.AdapterOptionDeref
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Refinement.AdapterInitEdPrimitive
/-- The two actual Ed25519 leaves retain invalid-key rejection and the opened owned buffer. -/
class Operations where
  PublicKey : Type
  Error : Type
  parse : Slice U8 → RustM (core.result.Result PublicKey Error)
  verify : Slice U8 → PublicKey → RustM (core.option.Option (alloc.vec.Vec U8))
end BeaconcryptCore.Refinement.AdapterInitEdPrimitive
namespace beaconcrypt_crypto.crypto_sign
abbrev PublicKey [operations : BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations] := operations.PublicKey

def PublicKey.from_bytes [operations : BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]
    (input : Slice U8) : RustM (core.result.Result PublicKey operations.Error) :=
  operations.parse input

def verify [operations : BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]
    (signed : Slice U8) (publicKey : PublicKey) : RustM (core.option.Option (alloc.vec.Vec U8)) :=
  operations.verify signed publicKey
end beaconcrypt_crypto.crypto_sign

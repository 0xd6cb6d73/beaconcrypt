-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterSealExtraction.Types

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.AdapterSealJoinCallbacks
/-! Generic joining stays an explicit callback until the separate fixed-two source helper is supplied. Optional failure and enclosing Rust failure/divergence remain distinct. -/
class Operations where
  join {N : Usize} : Array (Slice U8) N → RustM (core.option.Option (alloc.vec.Vec U8))
end BeaconcryptCore.Refinement.AdapterSealJoinCallbacks

namespace beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf

def Key.Insts.CoreConvertFromArrayU832
    [operations : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations] :
    core.convert.From Key (Array U8 32#usize) := { «from» := operations.fromKey }

def Nonce.Insts.CoreConvertFromArrayU812
    [operations : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations] :
    core.convert.From Nonce (Array U8 12#usize) := { «from» := operations.fromNonce }

def encrypt_detached [operations : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (plaintext : Slice U8) (associated : core.option.Option (Slice U8)) (nonce : Nonce) (key : Key) :
    RustM (core.result.Result (alloc.vec.Vec U8 × alloc.vec.Vec U8) operations.Error) :=
  operations.aead plaintext associated nonce key

end beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf

namespace beaconcrypt_seal

def ratchet.join_record_parts [operations : BeaconcryptCore.Refinement.AdapterSealJoinCallbacks.Operations]
    {N : Usize} (parts : Array (Slice U8) N) : RustM (core.option.Option (alloc.vec.Vec U8)) :=
  operations.join parts

end beaconcrypt_seal

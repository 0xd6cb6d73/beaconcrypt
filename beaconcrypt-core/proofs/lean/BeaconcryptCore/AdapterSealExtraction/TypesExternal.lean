-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterSealPrimitive
import BeaconcryptCore.AdapterPublicWrapperExtraction.TypesExternal

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

/-! The source AEAD request types are the existing extracted Core types. Key and nonce representations come from explicit operations. Zeroizing uses the selected wrapper representation already provided by the public-wrapper model; creation/dereference retain the selected value, and no drop or memory-erasure correspondence is claimed. -/

namespace beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf

abbrev Key [operations : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations] := operations.Key
abbrev Nonce [operations : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations] := operations.Nonce

end beaconcrypt_crypto.crypto_aead.chacha20poly1305_ietf

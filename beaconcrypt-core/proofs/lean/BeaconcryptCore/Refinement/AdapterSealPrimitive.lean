-- SPDX-License-Identifier: 0BSD
import Aeneas
import CoreModels

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true

/-! Explicit conversion and detached-AEAD interfaces for the original seal dispatcher. Every operation retains Rust failure/divergence and the AEAD result retains primitive rejection. No functional, totality, allocation, zeroization or security law is assumed. -/

namespace BeaconcryptCore.Refinement.AdapterSealPrimitive

class Operations where
  Key : Type
  Nonce : Type
  Error : Type
  fromKey : Array U8 32#usize → RustM Key
  fromNonce : Array U8 12#usize → RustM Nonce
  aead : Slice U8 → core.option.Option (Slice U8) → Nonce → Key →
    RustM (core.result.Result (alloc.vec.Vec U8 × alloc.vec.Vec U8) Error)

end BeaconcryptCore.Refinement.AdapterSealPrimitive

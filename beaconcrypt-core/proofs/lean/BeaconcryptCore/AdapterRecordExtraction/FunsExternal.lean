-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Extraction.Funs
import BeaconcryptCore.AdapterRecordExtraction.Types

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option autoImplicit false
set_option warningAsError true

namespace beaconcrypt.ratchet

/-! Explicit primitive implementations for the generated production record receiver. The hash wrapper returns both its optional digest and its complete updated transcript, so the generated borrow continuation retains every wrapper effect, including erasure on hash failure. Native primitive correctness and physical erasure remain separate obligations. -/
class Operations where
  kdf : beaconcrypt_core.ratchet.SymmetricRatchetKdfRequest →
    RustM beaconcrypt_core.ratchet.RatchetKdfResponse
  hash : beaconcrypt_core.commitment.CommitmentTranscript →
    RustM ((core.option.Option (Array Std.U8 64#usize)) ×
      beaconcrypt_core.commitment.CommitmentTranscript)
  aead : core.option.Option beaconcrypt_core.record.AeadRequest →
    RustM (core.option.Option (alloc.vec.Vec Std.U8))
  compare : Slice Std.U8 → Slice Std.U8 → RustM Bool

def ratchet_hkdf [operations : Operations]
    (request : beaconcrypt_core.ratchet.SymmetricRatchetKdfRequest) :
    RustM beaconcrypt_core.ratchet.RatchetKdfResponse := operations.kdf request

def execute_commitment_hash [operations : Operations]
    (transcript : beaconcrypt_core.commitment.CommitmentTranscript) :
    RustM ((core.option.Option (Array Std.U8 64#usize)) ×
      beaconcrypt_core.commitment.CommitmentTranscript) := operations.hash transcript

def execute_open_request [operations : Operations]
    (request : core.option.Option beaconcrypt_core.record.AeadRequest) :
    RustM (core.option.Option (alloc.vec.Vec Std.U8)) := operations.aead request

end beaconcrypt.ratchet

namespace beaconcrypt_crypto.utils

/-- The native constant-time comparison remains an explicit primitive implementation. -/
def memcmp [operations : beaconcrypt.ratchet.Operations]
    (left right : Slice Std.U8) : RustM Bool := operations.compare left right

end beaconcrypt_crypto.utils

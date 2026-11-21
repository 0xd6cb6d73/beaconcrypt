-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterRecordSendExtraction.Types
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace beaconcrypt_record_send.ratchet
/-! The source driver has exactly four effectful local leaves. Optional replies and the mutable commitment replacement remain literal. Their concrete source request interpreters are connected separately; physical erasure is outside this interface. -/
class Operations where
  kdf : beaconcrypt_core.ratchet.SymmetricRatchetKdfRequest → RustM beaconcrypt_core.ratchet.RatchetKdfResponse
  sealing : beaconcrypt_core.record_effects.AeadSealRequest → RustM (core.option.Option (alloc.vec.Vec U8 × Array U8 16#usize))
  hash : beaconcrypt_core.commitment.CommitmentTranscript → RustM (core.option.Option (Array U8 64#usize) × beaconcrypt_core.commitment.CommitmentTranscript)
  writer : beaconcrypt_core.record_effects.RecordWriteRequest → RustM (core.option.Option (alloc.vec.Vec U8))
def ratchet_hkdf [operations : Operations] := operations.kdf
def execute_seal_request [operations : Operations] := operations.sealing
def execute_commitment_hash [operations : Operations] := operations.hash
def execute_write_request [operations : Operations] := operations.writer
end beaconcrypt_record_send.ratchet

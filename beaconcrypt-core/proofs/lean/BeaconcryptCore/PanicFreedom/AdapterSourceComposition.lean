-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterRecordSend
import BeaconcryptCore.PanicFreedom.AdapterSeal
import BeaconcryptCore.PanicFreedom.AdapterRecordRouting

/-! Source-selected send callbacks discharge their normality from the native seal, fixed-two join, routing, fixed-three helpers and allocation certificates. Only KDF, commitment hash, primitive conversion/AEAD and reservation execution contracts remain external. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.PanicFreedom.AdapterSourceComposition
open Refinement
variable [primitives : AdapterSealPrimitive.Operations]
variable [allocator : AdapterWirePrimitive.Operations] [FrameDispatchFallback.Operations]

@[instance_reducible] def sendOperations
    (kdf : ratchet.SymmetricRatchetKdfRequest → RustM ratchet.RatchetKdfResponse)
    (hash : commitment.CommitmentTranscript →
      RustM (core.option.Option (Array U8 64#usize) × commitment.CommitmentTranscript))
    (sealFallback : AdapterSealJoinCallbacks.Operations)
    (writerFallback : RecordRoutingCallbacks.Operations) : beaconcrypt_record_send.ratchet.Operations where
  kdf := kdf
  hash := hash
  sealing request := @beaconcrypt_seal.ratchet.execute_seal_request primitives
    (AdapterSealSourceJoin.sourceCallbacks sealFallback) request
  writer request := @beaconcrypt_record_routing.ratchet.execute_write_request
    (AdapterRecordHelperRouting.sourceCallbacks writerFallback) request

theorem send_total
    (kdf : ratchet.SymmetricRatchetKdfRequest → RustM ratchet.RatchetKdfResponse)
    (hash : commitment.CommitmentTranscript →
      RustM (core.option.Option (Array U8 64#usize) × commitment.CommitmentTranscript))
    (kdfNormal : ∀ request, ∃ result, kdf request = ok result)
    (hashNormal : ∀ transcript, ∃ result, hash transcript = ok result)
    (crypto : AdapterSeal.PrimitiveContracts) (allocation : AdapterWire.Contracts)
    (sealFallback : AdapterSealJoinCallbacks.Operations)
    (writerFallback : RecordRoutingCallbacks.Operations)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (context : record_effects.SealFrameContext) :
    ∃ result, @beaconcrypt_record_send.ratchet.execute_record_send
      (sendOperations kdf hash sealFallback writerFallback) kernel context = ok result := by
  exact @AdapterRecordSend.execute_record_send_total (sendOperations kdf hash sealFallback writerFallback)
    (@AdapterRecordSend.Contracts.mk (sendOperations kdf hash sealFallback writerFallback)
      kdfNormal
      (AdapterSeal.execute_seal_request_source_total crypto allocation sealFallback)
      hashNormal
      (AdapterRecordRouting.source_callbacks_total allocation writerFallback)) kernel context

end BeaconcryptCore.PanicFreedom.AdapterSourceComposition

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterNormal
import BeaconcryptCore.PanicFreedom.AdapterRegistrationWriter
import BeaconcryptCore.Computational.RegistrationNativeSourceEncoders

/-! Public callers serialize the exact packets borrowed from signed core views. These interfaces select one writer and allocator for the complete execution. They impose no law on other packets or arbitrary output buffers. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.PanicFreedom.AdapterRegistrationWriterCallers
open Refinement AdapterNormal
open BeaconcryptCore.Computational.RegistrationNativeSourceEncoders (initSyntax responseSyntax)

/-- The six literal array borrows immediately before both native Beacon writer calls. -/
theorem init_packet_exact (view : registration.SignedInitView) :
    (do
      let identity ← lift (Array.to_slice view.fields.identity_key)
      let prekey ← lift (Array.to_slice view.fields.pre_key)
      let oneTime ← lift (Array.to_slice view.fields.one_time_key)
      let pq ← lift (Array.to_slice view.fields.pq_key)
      let mldsa ← lift (Array.to_slice view.fields.mldsa_public_key)
      let signature ← lift (Array.to_slice view.signature)
      ok (⟨identity, prekey, oneTime, pq, mldsa, signature⟩ : beaconcrypt_parse.transport.initkex)) =
      ok (initSyntax view) := rfl

/-- The literal response packet also retains the assigned id and selected application ciphertext. -/
theorem response_packet_exact (view : registration.SignedResponseView) :
    (do
      let identity ← lift (Array.to_slice view.identity_key)
      let ephemeral ← lift (Array.to_slice view.ephemeral_key)
      let kem ← lift (Array.to_slice view.kem_cipher_text)
      let signature ← lift (Array.to_slice view.signature)
      ok (⟨identity, ephemeral, kem, view.application_ciphertext, view.key_id, signature⟩ :
        beaconcrypt_parse.transport.kexresponse)) = ok (responseSyntax view) := rfl

variable [writer : RegistrationWriterPrimitive.Operations] [allocator : AdapterWirePrimitive.Operations]

structure InitCallerContracts : Prop where
  encode : ∀ view : registration.SignedInitView,
    Normal (beaconcrypt_registration_writer.wire.encode_init (initSyntax view))

structure ResponseCallerContracts : Prop where
  encode : ∀ view : registration.SignedResponseView,
    Normal (beaconcrypt_registration_writer.wire.encode_response (responseSyntax view))

/-- The reached native argument is exactly the packet borrowed from this signed view. -/
theorem init_native_total (contracts : InitCallerContracts) (view : registration.SignedInitView) :
    Normal (beaconcrypt_registration_writer.wire.encode_init
      ⟨view.fields.identity_key.to_slice, view.fields.pre_key.to_slice,
        view.fields.one_time_key.to_slice, view.fields.pq_key.to_slice,
        view.fields.mldsa_public_key.to_slice, view.signature.to_slice⟩) :=
  contracts.encode view

theorem response_native_total (contracts : ResponseCallerContracts) (view : registration.SignedResponseView) :
    Normal (beaconcrypt_registration_writer.wire.encode_response
      ⟨view.identity_key.to_slice, view.ephemeral_key.to_slice, view.kem_cipher_text.to_slice,
        view.application_ciphertext, view.key_id, view.signature.to_slice⟩) :=
  contracts.encode view

theorem init_of_all_packets (contracts : AdapterRegistrationWriter.Contracts)
    (allocation : AdapterWire.Contracts) : InitCallerContracts :=
  ⟨fun view => AdapterRegistrationWriter.encode_init_total contracts allocation (initSyntax view)⟩

theorem response_of_all_packets (contracts : AdapterRegistrationWriter.Contracts)
    (allocation : AdapterWire.Contracts) : ResponseCallerContracts :=
  ⟨fun view => AdapterRegistrationWriter.encode_response_total contracts allocation (responseSyntax view)⟩

end BeaconcryptCore.PanicFreedom.AdapterRegistrationWriterCallers

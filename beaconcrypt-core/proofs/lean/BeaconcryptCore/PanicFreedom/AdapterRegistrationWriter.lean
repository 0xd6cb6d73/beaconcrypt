-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterWire
import BeaconcryptCore.PanicFreedom.Transport
import BeaconcryptCore.AdapterRegistrationWriterExtraction.Funs

/-! Native registration serialization safety. Both schema writers may return zero or arbitrary normal mutable-buffer replies; protocol length rejection and allocator refusal remain ordinary returns. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.PanicFreedom.AdapterRegistrationWriter
open Refinement
variable [writer : RegistrationWriterPrimitive.Operations]
variable [allocator : AdapterWirePrimitive.Operations]

structure Contracts : Prop where
  encodeInit : ∀ value bytes, ∃ result, writer.encodeInit value bytes = ok result
  encodeResponse : ∀ value bytes, ∃ result, writer.encodeResponse value bytes = ok result

omit allocator in
theorem encode_init_closure_total (contracts : Contracts)
    (value : beaconcrypt_registration_writer.wire.encode_init.closure) (bytes : Slice U8) :
    ∃ result, beaconcrypt_registration_writer.wire.encode_init.closure.Insts.CoreOpsFunctionFnOnceTupleMutSliceU8Usize.call_once
      value bytes = ok result := contracts.encodeInit value bytes

omit allocator in
theorem encode_response_closure_total (contracts : Contracts)
    (value : beaconcrypt_registration_writer.wire.encode_response.closure) (bytes : Slice U8) :
    ∃ result, beaconcrypt_registration_writer.wire.encode_response.closure.Insts.CoreOpsFunctionFnOnceTupleMutSliceU8Usize.call_once
      value bytes = ok result := contracts.encodeResponse value bytes

theorem encode_init_total (contracts : Contracts) (allocation : AdapterWire.Contracts)
    (value : beaconcrypt_parse.transport.initkex) :
    ∃ result, beaconcrypt_registration_writer.wire.encode_init value = ok result := by
  obtain ⟨capacity, sized⟩ := Transport.encoded_init_len_total
    (Array.make 6#usize [value.identity_key.len, value.pre_key.len, value.one_time_key.len,
      value.pq_key.len, value.mldsa_public_key.len, value.signature.len])
  cases capacity with
  | none =>
    exact ⟨.None, by simp! only [beaconcrypt_registration_writer.wire.encode_init,
      core.slice.Slice.len, rust_primitives.slice.slice_length, sized,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
      bind_tc_ok]⟩
  | some capacity =>
    simpa only [beaconcrypt_registration_writer.wire.encode_init,
      core.slice.Slice.len, rust_primitives.slice.slice_length, sized,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      bind_tc_ok] using AdapterWire.encode_record_total allocation
        beaconcrypt_registration_writer.wire.encode_init.closure.Insts.CoreOpsFunctionFnOnceTupleMutSliceU8Usize
        capacity value contracts.encodeInit

theorem encode_response_total (contracts : Contracts) (allocation : AdapterWire.Contracts)
    (value : beaconcrypt_parse.transport.kexresponse) :
    ∃ result, beaconcrypt_registration_writer.wire.encode_response value = ok result := by
  obtain ⟨capacity, sized⟩ := Transport.encoded_response_len_total
    (Array.make 5#usize [value.identity_key.len, value.ephemeral_key.len,
      value.kem_cipher_text.len, value.app_cipher_text.len, value.signature.len]) value.key_id
  cases capacity with
  | none =>
    exact ⟨.None, by simp! only [beaconcrypt_registration_writer.wire.encode_response,
      core.slice.Slice.len, rust_primitives.slice.slice_length, sized,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
      bind_tc_ok]⟩
  | some capacity =>
    simpa only [beaconcrypt_registration_writer.wire.encode_response,
      core.slice.Slice.len, rust_primitives.slice.slice_length, sized,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      bind_tc_ok] using AdapterWire.encode_record_total allocation
        beaconcrypt_registration_writer.wire.encode_response.closure.Insts.CoreOpsFunctionFnOnceTupleMutSliceU8Usize
        capacity value contracts.encodeResponse

end BeaconcryptCore.PanicFreedom.AdapterRegistrationWriter

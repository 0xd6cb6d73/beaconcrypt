-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.PanicFreedom.AdapterRegistrationWriter
import BeaconcryptCore.PanicFreedom.AdapterNormal
import BeaconcryptCore.PanicFreedom.AdapterRegistrationWriterCallers
import BeaconcryptCore.Computational.RegistrationNativeSourceEncoders

/-! Direct native registration writers select the maintained source serializers. Only the packet shape produced by a signed core view is required; the actual adapter size check supplies output capacity. Reservation refusal and complete-message size rejection remain normal returns. No universal packet/buffer serializer contract is assumed. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace BeaconcryptCore.PanicFreedom.AdapterRegistrationWriterSource
open Refinement AdapterNormal
open BeaconcryptCore.Computational
open RegistrationSerializerReachableSource (OtherBranches)
open RegistrationNativeSourceEncoders (sourceOperations initSyntax responseSyntax)
variable [allocator : AdapterWirePrimitive.Operations]
attribute [local irreducible] beaconcrypt_parse.extraction_encode_init beaconcrypt_parse.extraction_encode_response
attribute [local irreducible] RegistrationNativeSourceEncoders.sourceOperations

omit allocator in
private theorem slice_len_from_length (input : Slice U8) (width : Usize)
    (same : input.length = width.val) : input.len = width := by
  apply UScalar.eq_of_val_eq
  simpa only [Slice.len_val] using same

omit allocator in
theorem init_capacity (value : beaconcrypt_parse.transport.initkex)
    (shape : RegistrationSerializerInitBytes.InitShape value) (capacity : Usize)
    (sized : transport.encoded_init_len
      (Array.make 6#usize [value.identity_key.len, value.pre_key.len, value.one_time_key.len,
        value.pq_key.len, value.mldsa_public_key.len, value.signature.len]) = ok (some capacity)) :
    capacity.val = 6757 := by
  rcases shape with ⟨identity, prekey, oneTime, pq, mldsa, signature⟩
  have length0 := slice_len_from_length value.identity_key 33#usize identity
  have length1 := slice_len_from_length value.pre_key 98#usize prekey
  have length2 := slice_len_from_length value.one_time_key 98#usize oneTime
  have length3 := slice_len_from_length value.pq_key 1249#usize pq
  have length4 := slice_len_from_length value.mldsa_public_key 1952#usize mldsa
  have length5 := slice_len_from_length value.signature 3309#usize signature
  obtain ⟨reply, actual, represented⟩ := TransportSizingBridge.encoded_current_init_len_exact
  have source : transport.encoded_init_len
      (Array.make 6#usize [value.identity_key.len, value.pre_key.len, value.one_time_key.len,
        value.pq_key.len, value.mldsa_public_key.len, value.signature.len]) = ok reply := by
    simpa only [length0, length1, length2, length3, length4, length5] using actual
  have same := RustM.ok.inj (source.symm.trans sized)
  subst reply
  exact Option.some.inj represented

omit allocator in
theorem response_capacity (value : beaconcrypt_parse.transport.kexresponse)
    (shape : RegistrationSerializerResponseBytes.ResponseShape value) (capacity : Usize)
    (sized : transport.encoded_response_len
      (Array.make 5#usize [value.identity_key.len, value.ephemeral_key.len,
        value.kem_cipher_text.len, value.app_cipher_text.len, value.signature.len]) value.key_id = ok (some capacity)) :
    capacity.val = RegistrationSerializerResponseBytes.totalLength value ∧
      RegistrationSerializerResponseBytes.totalLength value ≤ CborSizing.maxMessageSize := by
  obtain ⟨reply, actual, represented⟩ := RegistrationSerializerResponseBytes.source_capacity value shape
  have same := RustM.ok.inj (actual.symm.trans sized)
  subst reply
  simp only [Refinement.Transport.absLength, Refinement.Transport.messageCap] at represented
  split_ifs at represented with admitted
  · exact ⟨Option.some.inj represented, admitted⟩

theorem init_total (allocation : AdapterWire.Contracts) (other : OtherBranches)
    (value : beaconcrypt_parse.transport.initkex) (shape : RegistrationSerializerInitBytes.InitShape value) :
    letI := sourceOperations other
    Normal (beaconcrypt_registration_writer.wire.encode_init value) := by
  let _ := sourceOperations other
  obtain ⟨capacity, sized⟩ := Transport.encoded_init_len_total
    (Array.make 6#usize [value.identity_key.len, value.pre_key.len, value.one_time_key.len,
      value.pq_key.len, value.mldsa_public_key.len, value.signature.len])
  cases capacity with
  | none =>
    exact ⟨none, by simp only [beaconcrypt_registration_writer.wire.encode_init,
      core.slice.Slice.len, rust_primitives.slice.slice_length, sized,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
      bind_tc_ok]⟩
  | some capacity =>
    have exactCapacity := init_capacity value shape capacity sized
    have room : 6757 ≤ (AdapterWireVector.zeros capacity).length := by
      simp only [AdapterWireVector.zeros, Slice.length, List.length_replicate]
      omega
    obtain ⟨after, serialized, _, _⟩ := RegistrationSerializerInitBytes.public_bytes
      other value (AdapterWireVector.zeros capacity) shape room
    have callback :
        beaconcrypt_registration_writer.wire.encode_init.closure.Insts.CoreOpsFunctionFnOnceTupleMutSliceU8Usize.call_once
          value (AdapterWireVector.zeros capacity) =
        @beaconcrypt_parse.extraction_encode_init (RegistrationSerializerReachableSource.operations other)
          value (AdapterWireVector.zeros capacity) := by
      unfold beaconcrypt_registration_writer.wire.encode_init.closure.Insts.CoreOpsFunctionFnOnceTupleMutSliceU8Usize.call_once
      exact RegistrationNativeSourceEncoders.runtime_init_binding other value (AdapterWireVector.zeros capacity)
    have serializerNormal : ∃ result,
        beaconcrypt_registration_writer.wire.encode_init.closure.Insts.CoreOpsFunctionFnOnceTupleMutSliceU8Usize.call_once
          value (AdapterWireVector.zeros capacity) = ok result := ⟨_, callback.trans serialized⟩
    simpa only [beaconcrypt_registration_writer.wire.encode_init,
      core.slice.Slice.len, rust_primitives.slice.slice_length, sized,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      bind_tc_ok] using AdapterWire.encode_record_total_at allocation
        beaconcrypt_registration_writer.wire.encode_init.closure.Insts.CoreOpsFunctionFnOnceTupleMutSliceU8Usize
        capacity value serializerNormal

theorem response_total (allocation : AdapterWire.Contracts) (other : OtherBranches)
    (value : beaconcrypt_parse.transport.kexresponse)
    (shape : RegistrationSerializerResponseBytes.ResponseShape value) :
    letI := sourceOperations other
    Normal (beaconcrypt_registration_writer.wire.encode_response value) := by
  let _ := sourceOperations other
  obtain ⟨capacity, sized⟩ := Transport.encoded_response_len_total
    (Array.make 5#usize [value.identity_key.len, value.ephemeral_key.len,
      value.kem_cipher_text.len, value.app_cipher_text.len, value.signature.len]) value.key_id
  cases capacity with
  | none =>
    exact ⟨none, by simp only [beaconcrypt_registration_writer.wire.encode_response,
      core.slice.Slice.len, rust_primitives.slice.slice_length, sized,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
      bind_tc_ok]⟩
  | some capacity =>
    obtain ⟨exactCapacity, admitted⟩ := response_capacity value shape capacity sized
    have room : RegistrationSerializerResponseBytes.totalLength value ≤
        (AdapterWireVector.zeros capacity).length := by
      simp only [AdapterWireVector.zeros, Slice.length, List.length_replicate]
      omega
    obtain ⟨after, serialized, _, _, _⟩ := RegistrationSerializerResponseBytes.public_bytes
      other value (AdapterWireVector.zeros capacity) shape room admitted
    have callback :
        beaconcrypt_registration_writer.wire.encode_response.closure.Insts.CoreOpsFunctionFnOnceTupleMutSliceU8Usize.call_once
          value (AdapterWireVector.zeros capacity) =
        @beaconcrypt_parse.extraction_encode_response (RegistrationSerializerReachableSource.operations other)
          value (AdapterWireVector.zeros capacity) := by
      unfold beaconcrypt_registration_writer.wire.encode_response.closure.Insts.CoreOpsFunctionFnOnceTupleMutSliceU8Usize.call_once
      exact RegistrationNativeSourceEncoders.runtime_response_binding other value (AdapterWireVector.zeros capacity)
    have serializerNormal : ∃ result,
        beaconcrypt_registration_writer.wire.encode_response.closure.Insts.CoreOpsFunctionFnOnceTupleMutSliceU8Usize.call_once
          value (AdapterWireVector.zeros capacity) = ok result :=
      ⟨_, callback.trans serialized⟩
    simpa only [beaconcrypt_registration_writer.wire.encode_response,
      core.slice.Slice.len, rust_primitives.slice.slice_length, sized,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      bind_tc_ok] using AdapterWire.encode_record_total_at allocation
        beaconcrypt_registration_writer.wire.encode_response.closure.Insts.CoreOpsFunctionFnOnceTupleMutSliceU8Usize
        capacity value serializerNormal

theorem init_view_total (allocation : AdapterWire.Contracts) (other : OtherBranches)
    (view : registration.SignedInitView) :
    letI := sourceOperations other
    Normal (beaconcrypt_registration_writer.wire.encode_init (initSyntax view)) :=
  init_total allocation other (initSyntax view) (RegistrationNativeSourceEncoders.init_shape view)

theorem response_view_total (allocation : AdapterWire.Contracts) (other : OtherBranches)
    (view : registration.SignedResponseView) :
    letI := sourceOperations other
    Normal (beaconcrypt_registration_writer.wire.encode_response (responseSyntax view)) :=
  response_total allocation other (responseSyntax view) (RegistrationNativeSourceEncoders.response_shape view)

theorem init_caller_contracts (allocation : AdapterWire.Contracts) (other : OtherBranches) :
    letI := sourceOperations other
    AdapterRegistrationWriterCallers.InitCallerContracts := by
  let _ := sourceOperations other
  exact ⟨init_view_total allocation other⟩

theorem response_caller_contracts (allocation : AdapterWire.Contracts) (other : OtherBranches) :
    letI := sourceOperations other
    AdapterRegistrationWriterCallers.ResponseCallerContracts := by
  let _ := sourceOperations other
  exact ⟨response_view_total allocation other⟩

end BeaconcryptCore.PanicFreedom.AdapterRegistrationWriterSource
